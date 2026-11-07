-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.Ex_comp_negBits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:13:56.786218+00:00
-- url     : https://prove2.me/submissions/6c999cec-fb57-4751-a1cd-984997628606

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {N : ℕ} (F : (Fin N → Bool) → ℝ) :
    Ex (fun X => F (negBits X)) = Ex F := by
  unfold Ex
  congr 1
  exact Equiv.sum_comp (negBitsEquiv N) F
end AaronsonAmbainis.Bridge
