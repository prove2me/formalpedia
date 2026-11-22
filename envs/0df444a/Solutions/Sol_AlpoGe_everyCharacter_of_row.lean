-- Prove2me | solution 1 for AlpoGe.everyCharacter_of_row
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @GeorgeCoote
-- created : 2026-11-21T21:06:05.204912+00:00
-- url     : https://prove2.me/submissions/31d41a03-d384-4ca7-bbd8-2108a815c853
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlpoGe_primitive_nonvanishing_below_record_of_row
import Theorems.Thm_TowardsGRH_LW56e2_b83dbbd_dirichlet_zero_free_bound

set_option autoImplicit false

theorem solution
    (H : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0 := by
  intro N _ χ s hs hpole
  rcases le_or_gt s.re (0.8749570698 : ℝ) with hupper | habove
  · have hs_ne_one : s ≠ 1 := by
      rintro rfl
      norm_num at hupper
    have hs_pos : 0 < s.re := lt_trans (by norm_num) hs
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hprimitive := AlpoGe.primitive_nonvanishing_below_record_of_row H χ.conductor
      χ.primitiveCharacter χ.primitiveCharacter_isPrimitive s hs hupper
    rw [← χ.changeLevel_primitiveCharacter,
      DirichletCharacter.LFunction_changeLevel _ _ (Or.inr hs_ne_one)]
    refine mul_ne_zero hprimitive (Finset.prod_ne_zero_iff.mpr ?_)
    intro p hp
    have hp_one : 1 < p := (Nat.prime_of_mem_primeFactors hp).one_lt
    have hpow : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_one.trans hp_one), Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp_one) (neg_neg_of_pos hs_pos)
    have hfactor : ‖χ.primitiveCharacter p * (p : ℂ) ^ (-s)‖ < 1 := by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (χ.primitiveCharacter.norm_le_one p)).trans_lt hpow
    intro hz
    rw [← sub_eq_zero.mp hz, norm_one] at hfactor
    exact (lt_irrefl 1) hfactor
  · exact TowardsGRH_LW56e2_b83dbbd.dirichlet_zero_free_bound χ habove fun h =>
      hpole.elim (fun hχ => hχ h.1) (fun hs' => hs' h.2)
