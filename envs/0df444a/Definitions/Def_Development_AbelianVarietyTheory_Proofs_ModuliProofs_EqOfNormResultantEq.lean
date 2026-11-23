-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEq
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:16:34.129724+00:00
-- url     : https://prove2.me/theorems/747d1cb1-6e9a-4efa-a3d1-dca18f73a2ea
-- title:
--   Eq Of Norm Resultant Eq
-- statement:
--   Definitions and structural lemmas for Eq Of Norm Resultant Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfNormResultantEq.lean

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
namespace ResultantNorm
open Polynomial Filter Topology
section Normed
variable {K Ω : Type} [NontriviallyNormedField K] [NormedField Ω] [NormedAlgebra K Ω]
end Normed
section Padic
variable {l : ℕ} [Fact l.Prime] {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]
end Padic
end ResultantNorm
end GlobalTheory


