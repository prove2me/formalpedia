-- Prove2me | solution 1 for AaronsonAmbainis.le_of_sq_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:18:33.210505+00:00
-- url     : https://prove2.me/submissions/18fa203f-190e-474d-bd76-8edc40dd4667

import Mathlib
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz

set_option autoImplicit true
open AaronsonAmbainis
open Finset
namespace AaronsonAmbainis
theorem _root_.solution {P C : ℝ} (hC : 0 ≤ C) (h : P ^ 2 ≤ C * P) : P ≤ C := by
  by_contra hcon
  have hlt : C < P := not_le.mp hcon
  have hPpos : 0 < P := lt_of_le_of_lt hC hlt
  nlinarith [mul_pos (sub_pos.mpr hlt) hPpos]
end AaronsonAmbainis
