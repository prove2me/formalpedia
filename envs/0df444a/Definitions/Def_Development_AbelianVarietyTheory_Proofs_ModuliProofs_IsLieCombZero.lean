-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsLieCombZero
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsLieCombZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:42:34.463918+00:00
-- url     : https://prove2.me/theorems/e663af8e-c057-4cb0-b8f1-97b9276bea66
-- title:
--   Is Lie Comb Zero
-- statement:
--   Definitions and structural lemmas for Is Lie Comb Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsLieCombZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsAlongGroupHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.SquareField
variable {K : Type} [Field K]
def zeroPt (K : Type) [Field K] : 𝟙_ (Over (Sp K)) ⟶ epsR K :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)
section
variable {A₁ A₀ : Over (Sp K)} [GrpObj A₁] [GrpObj A₀] (f : A₁ ⟶ A₀) [IsMonHom f]
  {w : epsR K ⟶ A₁} {dw : ∀ O : A₁.left.Opens, Γ(A₁.left, O) → Γ(A₁.left, O)}
end
end GlobalTheory.KS.SquareField
end


