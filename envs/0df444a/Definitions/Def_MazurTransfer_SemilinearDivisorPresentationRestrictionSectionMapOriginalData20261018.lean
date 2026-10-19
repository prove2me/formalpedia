-- Prove2me | Definitions.Def_MazurTransfer_SemilinearDivisorPresentationRestrictionSectionMapOriginalData20261018
-- name    : MazurTransfer_SemilinearDivisorPresentationRestrictionSectionMapOriginalData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T13:29:21.960897+00:00
-- url     : https://prove2.me/theorems/6f5a0c09-77b7-49bb-842c-f83fb9cca693
-- title:
--   Original semilinear divisor-presentation restriction section map
-- statement:
--   Preserve the complete original section-map constructor for an open-immersion restriction followed by a specified semilinear function-field automorphism. The complete original type and nonproof value are checked. This interface asserts no presentation transport premise or conclusion; its named downstream consumer is SemilinearCurveIsoDivisorPresentationFieldAction.presentation_pullback and the actual Galois divisor-presentation theorem.
-- source:
--   MazurTheorem SemilinearDivisorPresentationRestrictionFieldAction.restrictionSectionMap; exact original constructor type and value.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: divisor presentations transport under semilinear
open-immersion pullback when the actual generic and place actions agree.
Named downstream consumer: SemilinearCurveIsoDivisorPresentationFieldAction.presentation_pullback, then actual Galois divisor-class naturality.
-/
import Definitions.Def_MazurTransfer_OriginalDivisorPresentationTransportDataExplicitSectionSpaces20261017
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

noncomputable section
universe u
namespace MazurTransfer.SemilinearDivisorPresentationRestrictionFieldAction
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
variable {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]
  (c : C ⟶ Spec (CommRingCat.of K))
variable (f : C ⟶ C) [IsOpenImmersion f] (g : letI := (baseToFunctionField c).toAlgebra; SemilinearAut K C.functionField)
  (L : C.Modules) (D : letI := (baseToFunctionField c).toAlgebra; Divisor K C.functionField)
  (φ : ∀ U : C.Opens, Γ(L, U) →+ (C.functionField : Type u))

def restrictionSectionMap (U : C.Opens) :
    Γ(L.restrict f, U) →+ (C.functionField : Type u) :=
  letI := (baseToFunctionField c).toAlgebra
  (SemilinearAut.toRingAut g).toAddMonoidHom.comp ((φ (f ''ᵁ U)).comp (L.restrictAppIso f U).hom.hom)


end MazurTransfer.SemilinearDivisorPresentationRestrictionFieldAction
#print axioms MazurTransfer.SemilinearDivisorPresentationRestrictionFieldAction.restrictionSectionMap


