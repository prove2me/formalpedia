-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSimTrivialOfMult
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSimTrivialOfMult
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:55.31265+00:00
-- url     : https://prove2.me/theorems/40bda68f-41b0-4cca-9a61-f2277a958d8d
-- title:
--   Exists Sim Trivial Of Mult
-- statement:
--   Definitions and structural lemmas for Exists Sim Trivial Of Mult, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSimTrivialOfMult.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.SimMult
section Ring
variable {O : Type*} [CommRing O] (σ : O →+* O)
end Ring
section Dedekind
variable {O : Type*} [CommRing O] (σ : O →+* O)
end Dedekind
section Level
variable {O : Type*} [CommRing O] (σ : O →+* O)
end Level
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
section Host
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)
end Host
end GlobalTheory.SimMult


