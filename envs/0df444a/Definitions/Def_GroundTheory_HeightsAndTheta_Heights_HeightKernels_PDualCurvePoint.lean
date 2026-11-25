-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualCurvePoint
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualCurvePoint
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:32:04.09149+00:00
-- url     : https://prove2.me/theorems/e7bbc7ea-2895-5e59-a11c-ab076cbff948
-- title:
--   PDual Curve Point
-- statement:
--   Definitions and structural lemmas for PDual Curve Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualCurvePoint.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
noncomputable section
namespace DualCurvePointAlt
section General
variable {B : Type} [Fintype B] {ι : B → Type} [∀ k, Fintype (ι k)]
set_option linter.unusedSectionVars false
end General
section Dual
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type} [Fintype T]
  [DecidableEq T]
set_option linter.unusedSectionVars false
abbrev constK (K : Type) [Field K] (i : ℕ) : K →+* ProjField K i :=
  (algebraMap (MvPolynomial (Fin i) K) (ProjField K i)).comp C
def linVal (w : Fin i → K) : ProjField K i :=
  algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (∑ j, C (w j) * X j)
end Dual
end DualCurvePointAlt
end
end GroundTheory.Heights₂.Heights


