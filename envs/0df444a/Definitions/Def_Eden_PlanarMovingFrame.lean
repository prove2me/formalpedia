-- Prove2me | Definitions.Def_Eden_PlanarMovingFrame
-- name    : Eden_PlanarMovingFrame
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:22:11.310691+00:00
-- url     : https://prove2.me/theorems/eab40a76-5cab-5f5a-a1eb-103aebcb5ed7
-- title:
--   Planar Moving Frame
-- statement:
--   Definitions and structural lemmas for Planar Moving Frame, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarMovingFrame.lean

import Definitions.Def_Eden_PlanarDerivative
set_option autoImplicit true
noncomputable section
namespace Eden
def planarMovingPerturbation (Ω t : ℝ) (p v : PlanarSpace) : PlanarSpace :=
  (planarRadialFrame p).symm ((planarAngularRotation Ω t).symm
    (fderiv ℝ (planarEvolution Ω t) p (planarRadialFrame p v)))
end Eden


