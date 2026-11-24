-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PMultiHomogMemCoord
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PMultiHomogMemCoord
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:27.399599+00:00
-- url     : https://prove2.me/theorems/ac3e29a7-47a3-4c7e-bb58-a0cf00dd5228
-- title:
--   PMulti Homog Mem Coord
-- statement:
--   Definitions and structural lemmas for PMulti Homog Mem Coord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PMultiHomogMemCoord.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
namespace MultiHomogMemCoordinate
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
end MultiHomogMemCoordinate
end GroundTheory.Heights₂.Heights


