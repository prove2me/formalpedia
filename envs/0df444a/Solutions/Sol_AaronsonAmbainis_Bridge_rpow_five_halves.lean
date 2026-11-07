-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.rpow_five_halves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:13:52.417108+00:00
-- url     : https://prove2.me/submissions/931d7ce9-0daa-4818-b616-52abd690ee02

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {ε : ℝ} (hε : 0 ≤ ε) : ε ^ ((5 : ℝ) / 2) = ε ^ 2 * Real.sqrt ε := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add' hε (by norm_num)]
  norm_num
end AaronsonAmbainis.Bridge
