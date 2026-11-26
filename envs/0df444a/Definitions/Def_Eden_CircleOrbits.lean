-- Prove2me | Definitions.Def_Eden_CircleOrbits
-- name    : Eden_CircleOrbits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:44:47.580222+00:00
-- url     : https://prove2.me/theorems/88f2d98b-b91e-5b44-9494-496297c85ded
-- title:
--   Circle Orbits
-- statement:
--   Definitions and structural lemmas for Circle Orbits, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CircleOrbits.lean

import Definitions.Def_Eden_PeriodicSets
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
set_option autoImplicit true
noncomputable section
open Set
namespace Eden
def forwardOrbit (c : ℝ) (p : PhaseSpace) : Set PhaseSpace :=
  {q | ∃ t : ℝ, 0 ≤ t ∧ evolution c t p = q}
end Eden


