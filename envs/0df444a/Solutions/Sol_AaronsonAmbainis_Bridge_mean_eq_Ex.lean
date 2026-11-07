-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.mean_eq_Ex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:23:28.037937+00:00
-- url     : https://prove2.me/submissions/36ff5bdb-8f9e-4139-8604-de9c525e871b

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {N : ℕ} (F : Cube (Fin N) → ℝ) : mean F = Ex F := by
  unfold mean Ex
  rw [Fintype.card_fin]
end AaronsonAmbainis.Bridge
