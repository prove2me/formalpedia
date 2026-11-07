-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.evPMt_bound_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:17:18.634544+00:00
-- url     : https://prove2.me/submissions/409ee2b9-acfb-47d1-b19f-e2d837164712

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Theorems.Thm_AaronsonAmbainis_Bridge_evPMt_eq

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {N : ℕ} (p : MvPolynomial (Fin N) ℝ) :
    (∀ X, |evPMt p X| ≤ 1) ↔ ∀ X, |evPM p X| ≤ 1 := by
  constructor
  · intro h X
    have hX := h (negBits X)
    rwa [evPMt_eq, negBits_negBits] at hX
  · intro h X
    rw [evPMt_eq]
    exact h (negBits X)
end AaronsonAmbainis.Bridge
