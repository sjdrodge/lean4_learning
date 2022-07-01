namespace Hidden

inductive Eq {α : Sort u} (a : α) : α → Prop where
  | intro : Eq a a

inductive Nonempty (α : Sort u) : Prop where
  | intro : α → Nonempty α

theorem elim_from_prop_is_bad
(choice : ∀{α}, Nonempty α → α) :
¬({α : Type u} → {x : α} → choice ⟨x⟩ = x) := by
  intro h
  let true' : ULift Bool := ⟨true⟩
  let false' : ULift Bool := ⟨false⟩
  have t_eq_f : true' = false' := h.symm.trans h
  have : true = false := congrArg ULift.down t_eq_f
  contradiction

def Or.by_cases [Decidable p] [Decidable q] {α : Sort u}
(h : p ∨ q) (fp : p → α) (fq : q → α) : α :=
  if hp : p then fp hp else
  if hq : q then fq hq else
  False.elim (Or.elim h hp hq)

def Nat.strong_rec {p : Nat → Sort u}
(h : (n : Nat) → ((m : Nat) → m < n → p m) → p n)
(n : Nat) : p n :=
  h n (aux n)
where
  aux : (n m : Nat) → m < n → p m
    | 0, m, h₁ => absurd h₁ (Nat.not_lt_zero m)
    | n+1, m, h₁ => Or.by_cases (Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h₁))
      (λ h₂ => h₂ ▸ h n (aux n))
      (λ h₂ => (aux n) m h₂)

end Hidden