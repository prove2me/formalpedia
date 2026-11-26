-- Prove2me | Definitions.Def_Eden_TorusAngles
-- name    : Eden_TorusAngles
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:51:38.085521+00:00
-- url     : https://prove2.me/theorems/e299b570-18ce-4872-b5d9-4d317e6315b7
-- title:
--   Torus Angles
-- statement:
--   Definitions and structural lemmas for Torus Angles, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusAngles.lean

import Definitions.Def_Eden_CircleOrbits
set_option autoImplicit true
noncomputable section
open Set
namespace Eden
def torusPoint (θ₁ θ₂ : ℝ) : PhaseSpace :=
  !₂[Real.cos θ₁, Real.sin θ₁, Real.cos θ₂, Real.sin θ₂, 0]
end Eden


