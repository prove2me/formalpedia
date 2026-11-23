-- Prove2me | solution 1 for AutoformalisationSCI.dSetL_two_eq_dSet
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:50:35.222469+00:00
-- url     : https://prove2.me/submissions/03b0851f-0a45-4ebf-87d7-e92717150331

import Mathlib
import Definitions.Def_AutoformalisationSCI_Poly

set_option autoImplicit false

open AutoformalisationSCI

private lemma quantVec_all_true :
    ∀ (r : ℕ) (q : Fin r → Bool) (_hq : ∀ i : Fin r, q i = true) (P : (Fin r → ℕ) → Prop),
      QuantVec r q P ↔ ∀ v : Fin r → ℕ, P v
  | 0, q, _, P => by
    simp only [QuantVec]
    constructor
    · intro h v
      have hv : v = Fin.elim0 := funext fun i => Fin.elim0 i
      exact hv ▸ h
    · intro h
      exact h Fin.elim0
  | r + 1, q, hq, P => by
    simp only [QuantVec, hq 0, ↓reduceIte]
    have ih := fun z : ℕ =>
      quantVec_all_true r (fun i => q i.succ) (fun i => hq i.succ) (fun zs => P (Fin.cons z zs))
    simp only [ih]
    constructor
    · intro h v
      have hv : Fin.cons (v 0) (Fin.tail v) = v := Fin.cons_self_tail v
      exact hv ▸ h (v 0) (Fin.tail v)
    · intro h z zs
      exact h (Fin.cons z zs)

private lemma eval_cast_enum {a b : ℕ} (hab : a = b) (E : ComputablePolyEnum a)
    (e : ℕ) (f : Fin b → ℤ) :
    MvPolynomial.eval f ((cast (congrArg ComputablePolyEnum hab) E).p e) =
      MvPolynomial.eval (fun i => f (Fin.cast hab i)) (E.p e) := by
  subst hab
  rfl

theorem solution (k : ℕ) (E : ComputablePolyEnum (k + 1)) :
    dSetL 2 k (by omega)
        (cast (congrArg ComputablePolyEnum (by omega : k + 1 = 2 - 1 + k)) E) =
      dSet k E := by
  ext e
  change (∃ n, Bgen 2 k (by omega)
    (cast (congrArg ComputablePolyEnum (by omega : k + 1 = 2 - 1 + k)) E) e n) ↔
    ∃ n, B k E e n
  refine exists_congr fun n => ?_
  unfold Bgen B
  have hq : ∀ i : Fin (2 - 2 + k), qtype 2 k i = true := fun _ => by simp [qtype]
  rw [quantVec_all_true (2 - 2 + k) (qtype 2 k) hq]
  have h_even : (2 : ℕ) % 2 = 0 := rfl
  simp only [h_even, ↓reduceIte]
  have eq0 : 2 - 2 + k = k := by omega
  constructor
  · intro hv x
    have hx := hv (fun j => x (Fin.cast eq0 j))
    rw [eval_cast_enum (by omega : k + 1 = 2 - 1 + k) E e] at hx
    have hfun :
        (fun i : Fin (k + 1) =>
          ((if h : (Fin.cast (by omega : 2 - 1 + k = 2 - 2 + k + 1)
              (Fin.cast (by omega : k + 1 = 2 - 1 + k) i)).val = 0
            then n
            else x (Fin.cast eq0 ⟨(Fin.cast (by omega : 2 - 1 + k = 2 - 2 + k + 1)
              (Fin.cast (by omega : k + 1 = 2 - 1 + k) i)).val - 1, by omega⟩) : ℕ) : ℤ)) =
        (fun i : Fin (k + 1) =>
          if h : i.val = 0 then (n : ℤ) else (x ⟨i.val - 1, by have := i.isLt; omega⟩ : ℤ)) := by
      ext i
      by_cases hi : i.val = 0 <;> simp [hi]
    rwa [hfun] at hx
  · intro hx v
    have hv := hx (fun j => v (Fin.cast eq0.symm j))
    rw [eval_cast_enum (by omega : k + 1 = 2 - 1 + k) E e]
    have hfun :
        (fun i : Fin (k + 1) =>
          ((if h : (Fin.cast (by omega : 2 - 1 + k = 2 - 2 + k + 1)
              (Fin.cast (by omega : k + 1 = 2 - 1 + k) i)).val = 0
            then n
            else v ⟨(Fin.cast (by omega : 2 - 1 + k = 2 - 2 + k + 1)
              (Fin.cast (by omega : k + 1 = 2 - 1 + k) i)).val - 1, by omega⟩ : ℕ) : ℤ)) =
        (fun i : Fin (k + 1) =>
          if h : i.val = 0 then (n : ℤ)
          else (v (Fin.cast eq0.symm ⟨i.val - 1, by have := i.isLt; omega⟩) : ℤ)) := by
      ext i
      by_cases hi : i.val = 0 <;> simp [hi]
    rwa [hfun]
