-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FderivFnAddLattice
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_FderivFnAddLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:55:54.733665+00:00
-- url     : https://prove2.me/theorems/fe7a204b-7de9-48d5-9e1c-03eb88c12ca8
-- title:
--   Fderiv Fn Add Lattice
-- statement:
--   Definitions and structural lemmas for Fderiv Fn Add Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FderivFnAddLattice.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EntireAntilinearLatticePeriodsConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDifferentiableOnVerticalVectorFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueUniformisingVectorVerticalTangentStatement
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
namespace GlobalTheory.KS.Uniq
section
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}
end
end GlobalTheory.KS.Uniq


