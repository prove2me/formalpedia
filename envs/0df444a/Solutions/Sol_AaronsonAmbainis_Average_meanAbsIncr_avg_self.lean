-- Prove2me | solution 1 for AaronsonAmbainis.Average.meanAbsIncr_avg_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:43:28.168606+00:00
-- url     : https://prove2.me/submissions/3dfd5b1e-57ca-467e-a1fd-2ff11d2b844e

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Average_Coordinate
import Theorems.Thm_AaronsonAmbainis_Average_avg_flip

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Average
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Average
theorem _root_.solution (j : ι) (f : Cube ι → ℝ) : meanAbsIncr (avg j f) j = 0 := by
  unfold meanAbsIncr
  rw [Finset.sum_eq_zero (fun x _ => by rw [avg_flip, sub_self, abs_zero]), zero_div]
end AaronsonAmbainis.Average
