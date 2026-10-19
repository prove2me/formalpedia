-- Prove2me | Definitions.Def_MazurTransfer_OriginalDivisorPresentationRestrictionSectionMapData
-- name    : MazurTransfer_OriginalDivisorPresentationRestrictionSectionMapData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T14:40:31.067571+00:00
-- url     : https://prove2.me/theorems/9947e3cd-91e3-4c2f-a3db-8ec05038dd69
-- title:
--   The original explicit section map for divisor-presentation restriction
-- statement:
--   For an integral scheme $C$ over a field, an open immersion $f:C\to C$, a specified function-field automorphism $\sigma$, an $\mathcal O_C$-module $L$ and additive section maps $\varphi_U$, the original transported section map is $$\psi_U=\sigma\circ\varphi_{f(U)}\circ r_U,$$ where $r_U$ is the canonical restriction-section isomorphism. This library records that exact constructor for the full divisor-presentation transport theorem.
-- source:
--   Original complete restrictionSectionMap declaration and body from MazurTheorem DivisorPresentationRestrictionFieldAction.lean, Apache-2.0, Vas and contributors. Its complete original closed type and single data value are kernel-compared. The original predicate and transport data use the checked official Anthropic FLT interface at 6e837e75355538c7f80bab5b956861e86c4eacc2. Named downstream consumer: the complete original divisor-presentation restriction contract, exposed with explicit binders and imports-only context.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the unchanged original section-map constructor for
transport of a divisor presentation under an open restriction and field action.
Named downstream consumer: the full divisor-presentation restriction theorem.
Original constructor statement and body retained from
DivisorPresentationRestrictionFieldAction.lean.
-/
import Definitions.Def_MazurTransfer_OriginalDivisorPresentationTransportDataExplicitSectionSpaces20261017
noncomputable section
universe u
namespace MazurTransfer.DivisorPresentationRestrictionFieldAction
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
variable {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]
  (c : C ⟶ Spec (CommRingCat.of K))
variable (f : C ⟶ C) [IsOpenImmersion f] (σ : letI := (baseToFunctionField c).toAlgebra; C.functionField ≃ₐ[K] C.functionField)
  (L : C.Modules) (D : letI := (baseToFunctionField c).toAlgebra; Divisor K C.functionField)
  (φ : ∀ U : C.Opens, Γ(L, U) →+ (C.functionField : Type u))

def restrictionSectionMap (U : C.Opens) :
    Γ(L.restrict f, U) →+ (C.functionField : Type u) :=
  σ.toAddMonoidHom.comp ((φ (f ''ᵁ U)).comp (L.restrictAppIso f U).hom.hom)

end MazurTransfer.DivisorPresentationRestrictionFieldAction
#print axioms MazurTransfer.DivisorPresentationRestrictionFieldAction.restrictionSectionMap


