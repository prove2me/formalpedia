-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_POneBlockPointDeg
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_POneBlockPointDeg
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:44:43.344325+00:00
-- url     : https://prove2.me/theorems/50fdf4be-10e4-4842-a6c4-109b1d708cc4
-- title:
--   POne Block Point Deg
-- statement:
--   Definitions and structural lemmas for POne Block Point Deg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/POneBlockPointDeg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartRankAdjoin
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
noncomputable section
namespace OneBlockPointDeg
variable {Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ'] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {k₀ : K}
end OneBlockPointDeg
end
end GroundTheory.Heights₂.Heights


