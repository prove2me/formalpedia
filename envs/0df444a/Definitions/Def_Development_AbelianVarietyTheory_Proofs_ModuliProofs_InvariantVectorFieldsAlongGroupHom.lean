-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsAlongGroupHom
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsAlongGroupHom
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:19.69483+00:00
-- url     : https://prove2.me/theorems/6b7f53b4-4428-48e8-bba3-d28a7de3ae97
-- title:
--   Invariant Vector Fields Along Group Hom
-- statement:
--   Definitions and structural lemmas for Invariant Vector Fields Along Group Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InvariantVectorFieldsAlongGroupHom.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningFieldStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieCombIffProd
import Theorems.Thm_GlobalTheory_PowLie_isTangent_iff

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
open GlobalTheory.PowLie (sc zeroPt isTangent_iff)
noncomputable section
namespace GlobalTheory.KS.InvHom
variable {K : Type} [Field K]
def jA (A : Over (Sp K)) : A ⟶ epsR K ⊗ A := lift (toUnit A ≫ zeroPt K) (𝟙 A)
abbrev tr {A : Over (Sp K)} [GrpObj A] (v : epsR K ⟶ A) : epsR K ⊗ A ⟶ A :=
  (fst (epsR K) A ≫ v) * snd (epsR K) A
variable {A : Over (Sp K)} [GrpObj A]
end GlobalTheory.KS.InvHom
end


