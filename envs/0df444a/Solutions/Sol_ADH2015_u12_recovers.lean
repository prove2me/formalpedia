-- Prove2me | solution 1 for ADH2015.u12_recovers
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:21:20.999685+00:00
-- url     : https://prove2.me/submissions/0b450f1a-c8b6-4b13-9453-9cb0e98d98e5

import Mathlib
import Definitions.Def_ADH2015_defs

open Matrix
open scoped Kronecker
open ADH2015

/-- Inverse of `u12Map`. -/
def adhU12Inv (y : Qutrit × Qutrit) : Qutrit × Qutrit :=
  (![![(0, 0), (1, 1), (2, 2)], ![(1, 2), (2, 0), (0, 1)], ![(2, 1), (0, 2), (1, 0)]] :
    Fin 3 → Fin 3 → Qutrit × Qutrit) y.1 y.2

lemma adhU12_map_iff (x y : Qutrit × Qutrit) : y = ADH2015.u12Map x ↔ x = adhU12Inv y := by
  revert x y; unfold ADH2015.u12Map adhU12Inv; decide

lemma adhU12_mulVec_kron (v : (Qutrit × Qutrit) × Qutrit → ℂ) :
    (ADH2015.U12 ⊗ₖ (1 : Matrix Qutrit Qutrit ℂ)) *ᵥ v = fun x => v (adhU12Inv x.1, x.2) := by
  funext x
  simp only [mulVec, dotProduct, kroneckerMap_apply, ADH2015.U12, of_apply]
  rw [Fintype.sum_eq_single (adhU12Inv x.1, x.2)]
  · rw [if_pos ((adhU12_map_iff _ _).2 rfl)]; simp
  · intro z hz
    by_cases h1 : x.1 = ADH2015.u12Map z.1
    · have h2 : x.2 ≠ z.2 := by
        intro h; exact hz (Prod.ext ((adhU12_map_iff _ _).1 h1) h.symm)
      simp [h1, one_apply, h2]
    · simp [h1]

lemma adhU12_cond (i : Qutrit) (x : (Qutrit × Qutrit) × Qutrit) :
    ((adhU12Inv x.1).2 = (adhU12Inv x.1).1 + i ∧ x.2 = (adhU12Inv x.1).1 + i + i) ↔
      (x.1.1 = i ∧ x.1.2 = x.2) := by
  revert i x; unfold adhU12Inv; decide

theorem solution :
    ADH2015.U12ᴴ * ADH2015.U12 = 1 ∧
    ∀ i : Qutrit, (ADH2015.U12 ⊗ₖ (1 : Matrix Qutrit Qutrit ℂ)) *ᵥ ADH2015.codeKet i =
      fun x => if x.1.1 = i ∧ x.1.2 = x.2 then ((1 / Real.sqrt 3 : ℝ) : ℂ) else 0 := by
  constructor
  · ext a b
    simp only [mul_apply, conjTranspose_apply, ADH2015.U12, of_apply]
    rw [Fintype.sum_eq_single (ADH2015.u12Map a)]
    · by_cases h : a = b
      · subst h; simp
      · have : ADH2015.u12Map a ≠ ADH2015.u12Map b := by
          intro e; apply h
          have hinj : Function.Injective ADH2015.u12Map := by
            unfold ADH2015.u12Map; decide
          exact hinj e
        simp [this, one_apply, h]
    · intro y hy; simp [hy]
  · intro i
    rw [adhU12_mulVec_kron]
    funext x
    simp only [ADH2015.codeKet]
    exact if_congr (adhU12_cond i x) rfl rfl
