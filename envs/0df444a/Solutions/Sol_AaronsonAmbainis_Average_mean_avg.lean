-- Prove2me | solution 1 for AaronsonAmbainis.Average.mean_avg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:41:57.750494+00:00
-- url     : https://prove2.me/submissions/af733bae-9c2b-4558-9540-8ac95e70e31f

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Average_Coordinate
import Theorems.Thm_AaronsonAmbainis_Average_sum_flip

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Average
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Average
theorem _root_.solution (j : ι) (f : Cube ι → ℝ) : mean (avg j f) = mean f := by
  unfold mean avg
  congr 1
  rw [← Finset.sum_div, Finset.sum_add_distrib, sum_flip j f]
  ring
end AaronsonAmbainis.Average
