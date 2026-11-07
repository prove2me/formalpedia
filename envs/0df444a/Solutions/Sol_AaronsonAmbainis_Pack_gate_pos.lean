-- Prove2me | solution 1 for AaronsonAmbainis.Pack.gate_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:43:30.199025+00:00
-- url     : https://prove2.me/submissions/6e1b3c75-8d65-43e7-85b1-b5c5cb3f3529

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Pack_Gate

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Pack
namespace AaronsonAmbainis.Pack
theorem _root_.solution (M : ℕ) (hM : 0 < M) : 0 < ⌈Real.pi * (M : ℝ) / 2⌉₊ := by
  have hMr : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  exact Nat.ceil_pos.mpr (div_pos (mul_pos hpi hMr) two_pos)
end AaronsonAmbainis.Pack
