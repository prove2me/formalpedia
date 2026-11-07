-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.variance_eq_zero_of_degree_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:23:15.532563+00:00
-- url     : https://prove2.me/submissions/993861f3-edb8-4626-af82-60460e924947

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_zero_const
import Theorems.Thm_AaronsonAmbainis_Level_variance_eq_zero_of_const


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {f : Cube ι → ℝ} (h : HasDegreeLE f 0) :
    variance f = 0 :=
  Level.variance_eq_zero_of_const f (hasDegreeLE_zero_const h)
end AaronsonAmbainis.Bridge
