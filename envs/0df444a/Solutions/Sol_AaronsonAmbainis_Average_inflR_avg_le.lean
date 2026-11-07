-- Prove2me | solution 1 for AaronsonAmbainis.Average.inflR_avg_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:42:05.92267+00:00
-- url     : https://prove2.me/submissions/55f4b5f9-a389-4283-a4c9-2c9e6d67a077

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
theorem _root_.solution (j k : ι) (f : Cube ι → ℝ) : inflR (avg j f) k ≤ inflR f k := by
  have hcomm : ∀ x : Cube ι, flipSet (flipSet x {k}) {j} = flipSet (flipSet x {j}) {k} :=
    fun x => flipSet_comm x {k} {j}
  have hpt : ∀ x, ((avg j f x - avg j f (flipSet x {k})) / 2) ^ 2
      ≤ (((f x - f (flipSet x {k})) / 2) ^ 2
        + ((f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k})) / 2) ^ 2) / 2 := by
    intro x
    unfold avg
    rw [hcomm x]
    nlinarith [sq_nonneg ((f x - f (flipSet x {k}))
      - (f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k})))]
  have hre : ∑ x, ((f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k})) / 2) ^ 2
      = ∑ x, ((f x - f (flipSet x {k})) / 2) ^ 2 :=
    sum_flip j (fun x => ((f x - f (flipSet x {k})) / 2) ^ 2)
  unfold inflR
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc ∑ x, ((avg j f x - avg j f (flipSet x {k})) / 2) ^ 2
      ≤ ∑ x, (((f x - f (flipSet x {k})) / 2) ^ 2
          + ((f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k})) / 2) ^ 2) / 2 :=
        Finset.sum_le_sum (fun x _ => hpt x)
    _ = ∑ x, ((f x - f (flipSet x {k})) / 2) ^ 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, hre]
        ring
end AaronsonAmbainis.Average
