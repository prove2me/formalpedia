-- Prove2me | Definitions.Def_Eden_TorusDirections
-- name    : Eden_TorusDirections
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:11:17.604915+00:00
-- url     : https://prove2.me/theorems/7dee6cb8-466f-45e6-92d5-f47d1729a1b3
-- title:
--   Torus Directions
-- statement:
--   Definitions and structural lemmas for Torus Directions, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusDirections.lean

import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_HausdorffDimensions
set_option autoImplicit true
noncomputable section
open Set Filter Topology MeasureTheory
namespace Eden
def radialOrthonormalBasis (p : PhaseSpace) : OrthonormalBasis (Fin 5) ℝ PhaseSpace :=
  (EuclideanSpace.basisFun (Fin 5) ℝ).map (radialFrame p)
end Eden


