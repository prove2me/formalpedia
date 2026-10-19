-- Prove2me | Definitions.Def_MazurTransfer_Order13RationalNormFixedKernelEquivalenceOriginalDataAndCertificatesExplicitRationalPointChangeV220261018
-- name    : MazurTransfer_Order13RationalNormFixedKernelEquivalenceOriginalDataAndCertificatesExplicitRationalPointChangeV220261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T20:05:50.266722+00:00
-- url     : https://prove2.me/theorems/5962560b-6b0e-498b-a5de-1e127756203f
-- title:
--   Original rational norm kernels as Galois-fixed geometric kernels
-- statement:
--   For the SAME represented Picard and each monoid endomorphism, rational norm-kernel points identify with the Galois-fixed geometric norm-kernel points. Four original constructors and five accompanying certificates retain their complete original types; all four nonproof constructor values are checked. The original group provider type and value and commutativity proof type are checked, as are two original scalar-extension proof helpers. Named downstream consumers: fixed norm-kernel cardinalities and invariant dimensions.
-- source:
--   MazurTheorem Order13ActualNormFixedKernelEquivalence and GaloisFixedOverPointDescent; original constructors, values and proof-helper propositions preserved; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: rational kernels of the SAME Picard norm maps are
isomorphic to the Galois-fixed subgroups of their geometric-point kernels.
Named downstream consumer: fixed dimensions of the actual norm-kernel
Galois modules in nineteen-isogeny descent.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardRationalFixedPointGroupData
import Definitions.Def_MazurTransfer_GaloisFixedOverPointScalarExtensionData
import Theorems.Thm_MazurTransfer_Order13ActualPicardGaloisFixedPointDescent_fixed_point_descends
noncomputable section
namespace MazurTransfer.RationalFixedKernelScalarExtensionProofHelpers20261018
open CategoryTheory AlgebraicGeometry
open FieldAutomorphismOverPointAction
variable (F K : Type) [Field F] [Field K] [Algebra F K]

open MazurTransfer.GaloisFixedOverPointDescent

theorem scalarMap_epi : Epi (fieldBase F K) := by
  letI : Surjective (fieldBase F K) := ⟨fun y => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective (fieldBase F K)

variable {F K} {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of F))

theorem scalarExtension_injective : Function.Injective
    (fun a : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ Over.mk t => scalarOverMap F K ≫ a) := by
  letI : Epi (fieldBase F K) := scalarMap_epi F K
  intro a a' h
  apply Over.OverMorphism.ext
  apply (cancel_epi (fieldBase F K)).mp
  exact congrArg Over.Hom.left h

end MazurTransfer.RationalFixedKernelScalarExtensionProofHelpers20261018

noncomputable section
namespace MazurTransfer.Order13ActualNormFixedKernelEquivalence
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles Order13ActualPicardGaloisFixedPointDescent
open scoped CategoryTheory.MonObj
local instance rationalFixedKernelOriginalGroupProvider20261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
local instance rationalFixedKernelOriginalCommutativeProvider20261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).isCommMonObj
variable (K : Type) [Field K] [CharZero K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]

def rationalNorm : RationalPoints →* RationalPoints where
  toFun a := a ≫ φ
  map_one' := MonObj.one_comp φ
  map_mul' a b := MonObj.mul_comp a b φ

def fixedNormKernel : Subgroup (Points K) := fixedPointGroup K ⊓ (normHom K φ).ker

theorem rationalPoint_comp (a : RationalPoints) :
    rationalPoint K (a ≫ φ) = rationalPoint K a ≫ φ := by
  exact (Category.assoc _ _ _).symm

def rationalKernelToFixed : (rationalNorm φ).ker →* fixedNormKernel K φ where
  toFun a := ⟨rationalPoint K a.val, ⟨
    fun σ => FieldAutomorphismOverPointAction.rationalPoint_fixed actualPicard.toBase σ a.val,
    by
      change rationalPoint K a.val ≫ φ = 1
      rw [← rationalPoint_comp, show (a.val ≫ φ) = 1 from a.property]
      exact map_one (rationalPointHom K)⟩⟩
  map_one' := Subtype.ext (map_one (rationalPointHom K))
  map_mul' a b := Subtype.ext (map_mul (rationalPointHom K) a.val b.val)

theorem rationalKernelToFixed_injective : Function.Injective (rationalKernelToFixed K φ) := by
  intro a b hab
  apply Subtype.ext
  apply (MazurTransfer.RationalFixedKernelScalarExtensionProofHelpers20261018.scalarExtension_injective (K := K) actualPicard.toBase)
  exact congrArg Subtype.val hab

variable [IsGalois ℚ K]

theorem rationalKernelToFixed_surjective : Function.Surjective (rationalKernelToFixed K φ) := by
  intro b
  obtain ⟨a, ha, _⟩ := fixed_point_descends K b.val b.property.1
  have hn : a ≫ φ = 1 := by
    apply (MazurTransfer.RationalFixedKernelScalarExtensionProofHelpers20261018.scalarExtension_injective (K := K) actualPicard.toBase)
    change rationalPoint K (a ≫ φ) = rationalPoint K 1
    rw [rationalPoint_comp, ha]
    exact b.property.2.trans (map_one (rationalPointHom K)).symm
  exact ⟨⟨a, hn⟩, Subtype.ext ha⟩

def rationalKernelFixedEquiv : (rationalNorm φ).ker ≃* fixedNormKernel K φ :=
  MulEquiv.ofBijective (rationalKernelToFixed K φ)
    ⟨rationalKernelToFixed_injective K φ, rationalKernelToFixed_surjective K φ⟩

theorem rationalKernelFixedEquiv_val (a : (rationalNorm φ).ker) :
    (rationalKernelFixedEquiv K φ a).val = rationalPoint K a.val := rfl

theorem fixedNormKernel_card : Nat.card (fixedNormKernel K φ) = Nat.card (rationalNorm φ).ker :=
  (Nat.card_congr (rationalKernelFixedEquiv K φ).toEquiv).symm

end MazurTransfer.Order13ActualNormFixedKernelEquivalence
#print axioms MazurTransfer.Order13ActualNormFixedKernelEquivalence.rationalKernelFixedEquiv
#print axioms MazurTransfer.Order13ActualNormFixedKernelEquivalence.fixedNormKernel_card


