-- Prove2me | Definitions.Def_Eden_VolumeGrowth
-- name    : Eden_VolumeGrowth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:18:40.485377+00:00
-- url     : https://prove2.me/theorems/d297638e-8461-4de4-a51d-88fa0e10ff72
-- title:
--   Volume Growth
-- statement:
--   Definitions and structural lemmas for Volume Growth, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeGrowth.lean

import Definitions.Def_Eden_FactorBounds
set_option autoImplicit true
noncomputable section
open Set
namespace Eden
def radialDefect (t s : ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..t, (squaredRadiusEvolution τ s - 1) ^ 2
def volumeDefect (t : ℝ) (p : PhaseSpace) : ℝ :=
  radialDefect t (radiusSq₁ p) + radialDefect t (radiusSq₂ p)
end Eden


