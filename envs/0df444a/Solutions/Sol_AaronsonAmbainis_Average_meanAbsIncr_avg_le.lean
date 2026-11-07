-- Prove2me | solution 1 for AaronsonAmbainis.Average.meanAbsIncr_avg_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:42:06.632655+00:00
-- url     : https://prove2.me/submissions/066fdcc7-cb3d-4a7d-8200-f3946ca74551

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Average_Coordinate
import Theorems.Thm_AaronsonAmbainis_Average_flipSet_comm
import Theorems.Thm_AaronsonAmbainis_Average_sum_flip

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Average
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Average
theorem _root_.solution (j k : ι) (f : Cube ι → ℝ) :
    meanAbsIncr (avg j f) k ≤ meanAbsIncr f k := by
  have hcomm : ∀ x : Cube ι, flipSet (flipSet x {k}) {j} = flipSet (flipSet x {j}) {k} :=
    fun x => flipSet_comm x {k} {j}
  have hpt : ∀ x, |avg j f x - avg j f (flipSet x {k})|
      ≤ (|f x - f (flipSet x {k})|
        + |f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k})|) / 2 := by
    intro x
    have e : avg j f x - avg j f (flipSet x {k})
        = ((f x - f (flipSet x {k}))
          + (f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k}))) / 2 := by
      unfold avg
      rw [hcomm x]
      ring
    rw [e, abs_div, abs_two]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
  have hre : ∑ x, |f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k})|
      = ∑ x, |f x - f (flipSet x {k})| :=
    sum_flip j (fun x => |f x - f (flipSet x {k})|)
  unfold meanAbsIncr
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc ∑ x, |avg j f x - avg j f (flipSet x {k})|
      ≤ ∑ x, (|f x - f (flipSet x {k})|
          + |f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k})|) / 2 :=
        Finset.sum_le_sum (fun x _ => hpt x)
    _ = ∑ x, |f x - f (flipSet x {k})| := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, hre]
        ring
end AaronsonAmbainis.Average
