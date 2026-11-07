-- Prove2me | solution 1 for AaronsonAmbainis.Average.exists_inflR_ge_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:31:59.078201+00:00
-- url     : https://prove2.me/submissions/eab15983-89d4-43c8-9218-0f9aa5429892

import Definitions.Def_AaronsonAmbainis_Average_Iterate
import Definitions.Def_AaronsonAmbainis_Average_Influence
import Theorems.Thm_AaronsonAmbainis_Average_pow_le_iff_sqrt_mul_le
import Theorems.Thm_AaronsonAmbainis_Level_inflR_nonneg
import Theorems.Thm_AaronsonAmbainis_Level_meanAbsIncr_nonneg


set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Average
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Average
theorem _root_.solution (hI : InfluenceBound) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    {K : ℝ} (ha : ∀ x i, 0 ≤ a x i) (hsum : ∀ x, ∑ i, a x i ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i) (hvar : 0 < variance f) :
    ∃ j, Real.sqrt 15 * (variance f ^ 2 * Real.sqrt (variance f))
      ≤ 125 * (∑ k, meanAbsIncr f k) * K ^ 2 * inflR f j := by
  obtain ⟨j, hj⟩ := hI ι f K a ha hsum hrow hvar
  exact ⟨j, (pow_le_iff_sqrt_mul_le hvar.le
    (Finset.sum_nonneg fun k _ => Level.meanAbsIncr_nonneg f k) (Level.inflR_nonneg f j)).mp hj⟩
end AaronsonAmbainis.Average
