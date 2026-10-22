-- Prove2me | Definitions.Def_MazurTransfer_OriginalSelectedPiMu19QuotientData20261020
-- name    : MazurTransfer_OriginalSelectedPiMu19QuotientData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-22T02:36:10.327185+00:00
-- url     : https://prove2.me/theorems/f7586440-ae05-4979-ac75-cb7357a469c0
-- title:
--   Original same selected pi quotient predicate in normalized literal mu19 coordinates
-- statement:
--   The checked normalized classification applies to the same finite flat quotient Hopf model and its same arithmetic root label. Freeness follows over the original local ring. Retain the original model, inclusion, injectivity, addition, Galois formula and selected pi restriction identity unchanged. The original scalar-change restriction square then identifies its literal mu19 quotient point with the previously selected piQuotient on the same original kernel label. Both complete original propositions and helper types, the whole original selected-model predicate, all twelve scoped provider types and four nonproof provider values, every generated helper type and all original chosen-map and point-operation contexts are independently checked. Named downstream consumer: pushforward of the actual integral pi norm-preimage torsor and its literal mu19 Kummer unit condition.
-- source:
--   MazurTheorem Order13SelectedPiMu19Quotient by Vas and contributors; same selected pi quotient and normalized literal mu19 model, Apache-2.0.

import Definitions.Def_MazurTransfer_Order13ActualPicardAlgebraicNormKummerEmbeddingsData
import Definitions.Def_MazurTransfer_OriginalActualIntegralCharacterQuotientsData20261020
import Definitions.Def_MazurTransfer_OriginalRationalSubringMu19ClassificationData20261020
import Definitions.Def_MazurTransfer_OriginalBialgebraBaseChangePointRestrictionData20261020
import Definitions.Def_MazurTransfer_OriginalBialgebraMu19QuotientPointsData20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: retain the SAME selected piQuotient model in NORMALIZED literal mu19 coordinates, bialgebra
inclusion, arithmetic label and restriction identity when classifying
its canonical scalar base change at nineteen. No replacement quotient.
Named downstream consumer: pushforward of the actual integral pi torsor
and its literal-mu19 Kummer unit condition.
-/

noncomputable section
namespace MazurTransfer.Order13SelectedPiMu19Quotient
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13SameIntegralPicardRationalSchemeComparison Order13LocalIntegralCoefficientMaps
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardSchemeNormGroupHom Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13IntegralRepresentationQuotient Order13ActualOrderedCharacterContinuousH1
open Order13RationalSubringBaseChange NineteenRootsGaloisRepresentation
open Order13RationalSubringMu19Classification CyclicNineteenGroupAlgebraPoints BialgebraCyclicMu19Points
open BialgebraBaseChangePointRestriction
open scoped CategoryTheory.MonObj TensorProduct
local notation "F" => AlgebraicClosure ℚ
local notation "R" => LocalRing 19
local notation "S" => GaloisRep.ratLocalizedAt 19
local instance instIsGaloisRatAlgebraicClosure_order13SelectedPiMu19Quotient : IsGalois ℚ F := Order13ActualPicardNormAlgebraicKummerInjection.canonicalClosureGalois
local instance instFactPrimeOfNatNat_order13SelectedPiMu19Quotient : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance instAlgebraLocalRingOfNatNatAlgebraicClosureRat_order13SelectedPiMu19Quotient : Algebra R F := Algebra.compHom F (algebraMap R ℚ)
local instance instIsScalarTowerLocalRingOfNatNatRatAlgebraicClosure_order13SelectedPiMu19Quotient : IsScalarTower R ℚ F := IsScalarTower.of_algebraMap_eq' rfl
local instance instIsScalarTowerLocalRingOfNatNatSubtypeRatMemSubringRatLocalizedAtAlgebraicClosure_order13SelectedPiMu19Quotient : IsScalarTower R S F :=
  localSubringTower 19 F (aRK := (inferInstance : Algebra R F))
    (tRQ := (inferInstance : IsScalarTower R ℚ F))
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13SelectedPiMu19Quotient : GrpObj (Over.mk actualPicard.toBase) := actualGroup
local instance instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13SelectedPiMu19Quotient : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance instIsMonHomOverSchemeSpecOfRatSchemePi_order13SelectedPiMu19Quotient : IsMonHom schemePi := schemePi_isMonHom
local instance instIsFiniteLeftSchemeSchemePi_order13SelectedPiMu19Quotient : IsFinite schemePi.left := MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoPiFiniteProvider20261018
local instance instFactForallEqSubtypePointsAlgebraicClosureRatMemSubgroupKernelSchemePiHPowOfNat_order13SelectedPiMu19Quotient : Fact (∀ z : Kernel F schemePi, z ^ 19 = 1) := ⟨pi_kernel_exponent_nineteen F⟩
local instance instModuleZModOfNatNatAdditiveSubtypePointsAlgebraicClosureRatMemSubgroupKernelSchemePi_order13SelectedPiMu19Quotient : Module (ZMod 19) (Additive (Kernel F schemePi)) := kernelZModModule F schemePi
local instance instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_order13SelectedPiMu19Quotient : Module (ZMod 19) (Additive (Roots F)) := rootsZModModule F

variable (z : F) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover)
variable (G : Type) [CommRing G] [HopfAlgebra R G]
variable (e : WithConv (G →ₐ[R] F) ≃ Additive (Kernel F schemePi))



def HasSelectedNormalizedMu19Quotient : Prop :=
  ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Free R H) (_ : Coalgebra.IsCocomm R H),
      Module.Flat R H ∧
      ∃ (j : H →ₐc[R] G) (e' : WithConv (H →ₐ[R] F) ≃ Additive (Roots F)),
        Function.Injective j ∧
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        (∀ (σ : F ≃ₐ[ℚ] F) (f g : WithConv (H →ₐ[R] F)),
          (∀ x : H, g x = σ (f x)) → e' g = rootsRepresentation F σ (e' f)) ∧
        (∀ f, e' (BialgebraPointRestriction.restrictPoint j f) = piQuotient F z hz 𝒱 (e f)) ∧
        ∃ ψ : (S ⊗[R] H) ≃ₐc[S] MonoidAlgebra S Cyclic,
          (∀ f : WithConv (S ⊗[R] H →ₐ[S] F), literalPointEquiv ψ F f =
            (e' (fixedBasePoint H f)).toMul) ∧
          ∀ f : WithConv (S ⊗[R] G →ₐ[S] F),
            BialgebraMu19QuotientPoints.quotientPoint (baseChangeMap («S» := S) j) ψ F f =
              (piQuotient F z hz 𝒱 (e (fixedBasePoint G f))).toMul



end MazurTransfer.Order13SelectedPiMu19Quotient

#print axioms MazurTransfer.Order13SelectedPiMu19Quotient.HasSelectedNormalizedMu19Quotient
#print axioms MazurTransfer.Order13SelectedPiMu19Quotient.instIsMonHomOverSchemeSpecOfRatSchemePi_order13SelectedPiMu19Quotient
#print axioms MazurTransfer.Order13SelectedPiMu19Quotient.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13SelectedPiMu19Quotient
#print axioms MazurTransfer.Order13SelectedPiMu19Quotient.instFactPrimeOfNatNat_order13SelectedPiMu19Quotient
#print axioms MazurTransfer.Order13SelectedPiMu19Quotient.instIsScalarTowerLocalRingOfNatNatSubtypeRatMemSubringRatLocalizedAtAlgebraicClosure_order13SelectedPiMu19Quotient
#print axioms MazurTransfer.Order13SelectedPiMu19Quotient.instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_order13SelectedPiMu19Quotient
#print axioms MazurTransfer.Order13SelectedPiMu19Quotient.instAlgebraLocalRingOfNatNatAlgebraicClosureRat_order13SelectedPiMu19Quotient
#print axioms MazurTransfer.Order13SelectedPiMu19Quotient.instIsFiniteLeftSchemeSchemePi_order13SelectedPiMu19Quotient
#print axioms MazurTransfer.Order13SelectedPiMu19Quotient.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13SelectedPiMu19Quotient
#print axioms MazurTransfer.Order13SelectedPiMu19Quotient.instIsGaloisRatAlgebraicClosure_order13SelectedPiMu19Quotient
#print axioms MazurTransfer.Order13SelectedPiMu19Quotient.instIsScalarTowerLocalRingOfNatNatRatAlgebraicClosure_order13SelectedPiMu19Quotient
#print axioms MazurTransfer.Order13SelectedPiMu19Quotient.instFactForallEqSubtypePointsAlgebraicClosureRatMemSubgroupKernelSchemePiHPowOfNat_order13SelectedPiMu19Quotient
#print axioms MazurTransfer.Order13SelectedPiMu19Quotient.instModuleZModOfNatNatAdditiveSubtypePointsAlgebraicClosureRatMemSubgroupKernelSchemePi_order13SelectedPiMu19Quotient


