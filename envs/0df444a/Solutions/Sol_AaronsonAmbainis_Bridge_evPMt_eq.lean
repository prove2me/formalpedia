-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.evPMt_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:13:47.924575+00:00
-- url     : https://prove2.me/submissions/b534f95d-e4cb-4193-959b-04e275232f56

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (X : Fin N → Bool) :
    evPMt p X = evPM p (negBits X) := by
  have hpt : (fun i => if X i then (1 : ℝ) else -1)
      = fun i => if negBits X i then (-1 : ℝ) else 1 := by
    funext i
    rcases Bool.eq_false_or_eq_true (X i) with h | h <;> simp [negBits, h]
  unfold evPMt evPM
  rw [hpt]
end AaronsonAmbainis.Bridge
