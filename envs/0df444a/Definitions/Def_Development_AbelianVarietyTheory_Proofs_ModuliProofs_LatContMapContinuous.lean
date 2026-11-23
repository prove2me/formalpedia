-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LatContMapContinuous
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_LatContMapContinuous
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:16.448653+00:00
-- url     : https://prove2.me/theorems/427308dc-3acd-498e-88a6-c6d6b88abd75
-- title:
--   Lat Cont Map Continuous
-- statement:
--   Definitions and structural lemmas for Lat Cont Map Continuous, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LatContMapContinuous.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory
noncomputable def latContMap {E J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype J]
    (v : J → E) : (J → ℝ) →L[ℝ] E :=
  ∑ i, (ContinuousLinearMap.proj i : (J → ℝ) →L[ℝ] ℝ).smulRight (v i)
end GlobalTheory


