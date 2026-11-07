-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.fourier_chi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:26:34.908974+00:00
-- url     : https://prove2.me/submissions/9483a9e7-800b-4ed4-99d2-2c76175073aa

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Theorems.Thm_AaronsonAmbainis_Bridge_sum_chi_mul_chi_cube

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (S T : Finset ι) : fourier (chi S) T = if S = T then 1 else 0 := by
  rw [fourier, sum_chi_mul_chi_cube]
  split_ifs
  · exact div_self (by positivity)
  · exact zero_div _
end AaronsonAmbainis.Bridge
