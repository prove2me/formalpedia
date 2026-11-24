-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobianOrderMonotoneSemistableModel
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobianOrderMonotoneSemistableModel
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T20:35:07.787123+00:00
-- url     : https://prove2.me/theorems/f11686b4-3573-4df8-88e3-247c0008889b
-- title:
--   Jacobian Order Monotone Semistable Model
-- statement:
--   Definitions and structural lemmas for Jacobian Order Monotone Semistable Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/JacobianOrderMonotoneSemistableModel.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ChainRuleAndJacobianCriterion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenImmersionOfExtendsIdOfEtale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.Ord
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GlobalTheory.SS.OrdMono
section
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}
  {I : Type} [Fintype I] [DecidableEq I]
abbrev IsCoord (M : Model R A) {I : Type} (U : M.Y.left.Opens) (t : I → Γ(M.Y.left, U)) : Prop :=
  (MvPolynomial.eval₂Hom (cst M U) t).Etale
abbrev jm (M : Model R A) (D : I → VF A) (U : M.Y.left.Opens) (t : I → Γ(M.Y.left, U)) : Γ(A.left, M.j ⁻¹ᵁ U) :=
  jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i))
end
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] {A : Over (Sp K)} {π : R} {I : Type} [Fintype I] [DecidableEq I]
section
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}
def th {X : Scheme.{0}} (W : X.Opens) : Γ(X, W) ⟶ Γ(W.toScheme, ⊤) := W.ι.appLE W ⊤ (by simp)
instance {X : Scheme.{0}} (W : X.Opens) : IsIso (th W) := by
  have : th W = W.topIso.inv := by simp [th, Scheme.Opens.topIso, Scheme.Opens.ι_appLE]; rfl
  rw [this]; infer_instance
end
end GlobalTheory.SS.OrdMono
end


