-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.sum_chi_mul_chi_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:24:52.471806+00:00
-- url     : https://prove2.me/submissions/a80b64c3-97e9-4523-8d9e-be69f262d869

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Theorems.Thm_AaronsonAmbainis_Bridge_chi_mul_chi
import Theorems.Thm_AaronsonAmbainis_Bridge_sum_chi

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (S T : Finset ι) :
    ∑ x : Cube ι, chi S x * chi T x = if S = T then (2 : ℝ) ^ Fintype.card ι else 0 := by
  simp only [chi_mul_chi, sum_chi, Finset.symmDiff_eq_empty]
end AaronsonAmbainis.Bridge
