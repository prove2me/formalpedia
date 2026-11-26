-- Prove2me | Definitions.Def_Eden_InstabilityGeometry
-- name    : Eden_InstabilityGeometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:24:36.922438+00:00
-- url     : https://prove2.me/theorems/5f351968-0284-54e7-9544-0acc1f71278f
-- title:
--   Instability Geometry
-- statement:
--   Definitions and structural lemmas for Instability Geometry, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InstabilityGeometry.lean

import Definitions.Def_Eden_UniformAttraction
import Definitions.Def_Eden_PeriodicOrbits
set_option autoImplicit true
noncomputable section
open Set
namespace Eden
def planeProjection (j : Fin 2) (p : PhaseSpace) : EuclideanSpace ℝ (Fin 2) :=
  if j = 0 then !₂[p 0, p 1] else !₂[p 2, p 3]
def radialPerturbation (j : Fin 2) (r s : ℝ) : PhaseSpace :=
  if j = 0 then !₂[r, 0, s, 0, 0] else !₂[s, 0, r, 0, 0]
end Eden


