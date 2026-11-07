-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.Ex_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:12:13.120415+00:00
-- url     : https://prove2.me/submissions/c9fe931e-5d81-4f07-bdea-56620318fca7

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {N : ℕ} {F : (Fin N → Bool) → ℝ} (hF : ∀ X, 0 ≤ F X) : 0 ≤ Ex F :=
  div_nonneg (Finset.sum_nonneg fun X _ => hF X) (by positivity)
end AaronsonAmbainis.Bridge
