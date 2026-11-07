-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.evalMat_dominant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:29:53.948077+00:00
-- url     : https://prove2.me/submissions/ba46db97-b9f2-42d6-b43a-3b333f147bf5

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_NonZero
import Theorems.Thm_AaronsonAmbainis_DetLow_agCount_self
import Theorems.Thm_AaronsonAmbainis_DetLow_agCount_lt
import Theorems.Thm_AaronsonAmbainis_DetLow_evalMat_apply
import Theorems.Thm_AaronsonAmbainis_DetLow_card_erase_succ_le

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution (g : Cube ι → Bool) (c : ℝ) (hc : c = 2 ^ Fintype.card ι)
    (x : Ones g) :
    ∑ z ∈ univ.erase x, ‖(evalAt c).mapMatrix (agMatrix g) x z‖
      < ‖(evalAt c).mapMatrix (agMatrix g) x x‖ := by
  have hc1 : (1 : ℝ) ≤ c := by
    rw [hc]
    exact one_le_pow₀ (by norm_num)
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc1
  have hcard : ((univ.erase x).card : ℝ) + 1 ≤ c := by
    rw [hc]
    exact_mod_cast card_erase_succ_le g x
  have hpow : 0 < c ^ Fintype.card ι := pow_pos hcpos _
  have hdiag : ‖(evalAt c).mapMatrix (agMatrix g) x x‖ = c ^ Fintype.card ι := by
    rw [evalMat_apply, agCount_self, Real.norm_of_nonneg (pow_nonneg hcpos.le _)]
  have hsum : (∑ z ∈ univ.erase x, ‖(evalAt c).mapMatrix (agMatrix g) x z‖) * c
      ≤ ((univ.erase x).card : ℝ) * c ^ Fintype.card ι := by
    rw [Finset.sum_mul]
    calc ∑ z ∈ univ.erase x, ‖(evalAt c).mapMatrix (agMatrix g) x z‖ * c
        ≤ ∑ _z ∈ univ.erase x, c ^ Fintype.card ι := by
          apply Finset.sum_le_sum
          intro z hz
          have hzx : x.1 ≠ z.1 := fun h => (Finset.ne_of_mem_erase hz) (Subtype.ext h.symm)
          rw [evalMat_apply, Real.norm_of_nonneg (pow_nonneg hcpos.le _), ← pow_succ]
          exact pow_le_pow_right₀ hc1 (agCount_lt x.1 z.1 hzx)
      _ = ((univ.erase x).card : ℝ) * c ^ Fintype.card ι := by
          rw [Finset.sum_const, nsmul_eq_mul]
  rw [hdiag]
  have hlt : (∑ z ∈ univ.erase x, ‖(evalAt c).mapMatrix (agMatrix g) x z‖) * c
      < c ^ Fintype.card ι * c := by
    calc (∑ z ∈ univ.erase x, ‖(evalAt c).mapMatrix (agMatrix g) x z‖) * c
        ≤ ((univ.erase x).card : ℝ) * c ^ Fintype.card ι := hsum
      _ < c * c ^ Fintype.card ι := by
          apply mul_lt_mul_of_pos_right _ hpow
          linarith
      _ = c ^ Fintype.card ι * c := mul_comm _ _
  exact lt_of_mul_lt_mul_right hlt hcpos.le
end AaronsonAmbainis.DetLow
