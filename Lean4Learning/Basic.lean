namespace Hidden


-- Notes on Lean's type theory:
-- In Lean, every expression `x` has a type `T`.
-- The notation `x : T` means "x has type T."
-- Furthermore, types are first-class citizens. They can appear freely
-- in expressions, not just in type signatures.
-- This means that in addition to normal things like
-- `true : Bool` and `5 : Nat`, we also have `Bool : Type` and `Nat : Type`.

-- Okay, great. It seems that the type of standard types is called `Type`,
-- but what about `Type` itself? You might be tempted to go with `Type : Type`,
-- but unfortunately this leads directly to Girard's Paradox
-- (the type theory analogue of Russell's Paradox for set theory).
-- The solution that Lean uses is to create an infinite hierarchy of so-called
-- "type universes." i.e., `Type : Type 1`, `Type 1 : Type 2`, etc.
-- Under this scheme, `Type` is just shorthand for `Type 0`.
-- Lean has a special additional type universe at the bottom of the hierarchy
-- `Prop : Type` which is intended for representing logical propositions.
-- Colectively, these type universes are called "sorts" and the following holds:
-- `Sort 0 = Prop`, `Sort (n+1) = Type n`.

-- The `Prop` universe has a few unique properties that set it apart:

-- Impredicativity: Normally, if `α : Sort u` and `β : Sort v`,
-- then `α → β : Sort max(u, v)`. However there's a special exception. if `β : Prop`,
-- then `α → β : Prop`. This is useful for defining predicates. Consider, for example:
-- `less_than_5 : Nat → Prop`

-- Proof Irrelevance: Every type in `Prop` is either empty or a singleton.
-- In other words, any two proofs of the same proposition are definitionally equal.
-- Furthermore, no details about the construction of a proof may be used unless
-- you are constructing another proof-irrelevant value (i.e. a proof of some `Prop`).
-- Without proof irrelevance, impredicativity would lead to a Girard-like paradox.


-- Creating new data types in Lean is done using so-called "inductive types."
-- To fully specify an inductive type, we must define a set of "introduction" rules
-- (how to construct the type) and "elimination" rules (how to destruct/use the type).
-- For an inductive type `T`, we define the introduction rules directly
-- when we define `T`'s constructors. The elimination rules are then provided
-- automatically by the compiler as a function `T.recOn`. Several examples follow.


-- This is the canonical false proposition. It is guaranteed to be uninhabited
-- because it has no constructors.
inductive False : Prop

#check False.recOn

-- This is the canonical true proposition. It is guaranteed to be inhabited
-- because it has a single constructor that takes no arguments.
inductive True : Prop where
  | intro : True

#check True.recOn

-- The negation of any proposition `p` is equivalent to the proposition
-- that `p` implies `False`.
def Not (p : Prop) : Prop := p → False

-- This is logical conjunction. It takes two propositions as type parameters.
-- It has a single constructor that takes proofs of each proposition as arguments.
inductive And (p q : Prop) : Prop where
  | intro : p → q → And p q

#check And.recOn

-- This is logical disjunction. It takes two propositions as type parameters.
-- It has two constructors, one for each proposition.
-- Each constructor takes a proof of the relevant proposition.
inductive Or (p q : Prop) : Prop where
  | inl : p → Or p q
  | inr : q → Or p q

#check Or.recOn

-- This is bidirectional implication. It takes two propositions as type
-- parameters. It has a single constructor which takes proofs of the
-- implication in each direction.
inductive Iff (p q : Prop) : Prop where
  | intro : (p → q) → (q → p) → Iff p q

#check Iff.recOn

-- This captures the notion of a proposition being decidable.
-- To construct a `Decidable p`, one must either provide a proof
-- of `p`, or a proof of `Not p`
-- Note also that `Decidable p` lives in `Type`, not `Prop`.
-- This allows us to avoid the "proof irrelevance" of `Prop` and
-- therefore freely eliminate into higher sorts.
-- Compare the `recOn` for `Decidable` and `DecidableProp` to see
-- this more clearly.
class inductive Decidable (p : Prop) : Type where
  | isFalse : Not p → Decidable p
  | isTrue : p → Decidable p

class inductive DecidableProp (p : Prop) : Prop where
  | isFalse : Not p → DecidableProp p
  | isTrue : p → DecidableProp p

#check Decidable.recOn
#check DecidableProp.recOn

-- The following two functions are used to provide `if ... then ... else ...`
-- syntax. Unlike most programming languages, the if doesn't take a boolean.
-- Instead, it takes a proposition `p` and an implicit `Decidable p`.
-- `dite` is used if either branch depends on `p` or `Not p`,
-- otherwise `ite` is used.
def dite {α : Sort u} (p : Prop) [dp : Decidable p]
(t : p → α) (e : Not p → α) : α :=
  Decidable.casesOn (motive := λ _ => α) dp e t

def ite {α : Sort u} (p : Prop) [Decidable p]
(t : α) (e : α) : α :=
  dite p (λ _ => t) (λ _ => e)

end Hidden