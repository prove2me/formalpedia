-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_pm_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:21:34.613613+00:00
-- url     : https://prove2.me/submissions/c2fdcc9c-0807-4f5f-897c-4d297546fecd

import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
import Theorems.Thm_AaronsonAmbainis_Bridge_dict_hasDegreeLE_one


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (i : ι) :
    HasDegreeLE (fun x : Cube ι => if x i then (-1 : ℝ) else 1) 1 :=
  dict_hasDegreeLE_one i
end AaronsonAmbainis.Bridge
