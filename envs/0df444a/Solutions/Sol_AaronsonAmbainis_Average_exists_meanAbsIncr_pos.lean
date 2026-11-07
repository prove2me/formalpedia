-- Prove2me | solution 1 for AaronsonAmbainis.Average.exists_meanAbsIncr_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:38:49.51912+00:00
-- url     : https://prove2.me/submissions/f34523d8-aead-479f-ac4a-582c8af39bcd

import Definitions.Def_AaronsonAmbainis_Average_Iterate
import Definitions.Def_AaronsonAmbainis_Average_Influence
import Theorems.Thm_AaronsonAmbainis_Level_meanAbsIncr_nonneg


set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Average
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Average
theorem _root_.solution (hMI : MeanIncrementBound) (g : Cube ι → ℝ) (b : Cube ι → ι → ℝ)
    {K : ℝ} (hb0 : ∀ x i, 0 ≤ b x i) (hbK : ∀ x, ∑ i, b x i ≤ K)
    (hbrow : ∀ x y, |g x - g y| ≤ ∑ i ∈ diffSet x y, b x i) (hg : 0 < variance g) :
    ∃ j, 0 < meanAbsIncr g j ∧ variance g ^ 3 ≤ 36 * K ^ 4 * meanAbsIncr g j ^ 2 := by
  obtain ⟨j, hj⟩ := hMI ι g K b hb0 hbK hbrow hg
  refine ⟨j, ?_, hj⟩
  by_contra h
  have h0 : meanAbsIncr g j = 0 := le_antisymm (not_lt.mp h) (Level.meanAbsIncr_nonneg g j)
  have h3 : 0 < variance g ^ 3 := pow_pos hg 3
  have e : 36 * K ^ 4 * (0 : ℝ) ^ 2 = 0 := by ring
  rw [h0, e] at hj
  linarith
end AaronsonAmbainis.Average
