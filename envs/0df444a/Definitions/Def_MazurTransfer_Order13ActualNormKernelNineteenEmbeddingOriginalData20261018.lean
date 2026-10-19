-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNormKernelNineteenEmbeddingOriginalData20261018
-- name    : MazurTransfer_Order13ActualNormKernelNineteenEmbeddingOriginalData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T15:05:15.521461+00:00
-- url     : https://prove2.me/theorems/15e72374-734f-4fcb-9a75-0d2762febb9f
-- title:
--   Original additive embeddings of actual nineteen-killed norm kernels into Picard torsion
-- statement:
--   The original additive embedding into the same actual Picard nineteen-torsion, its restriction to the corresponding torsion norm kernel, and the induced equivalence. The three constructor values and six declaration types, including injectivity, norm-zero and surjectivity laws, are checked against the complete original module. Thirteen group, Galois-action, finiteness and F19-module provider types and six nonproof provider values are checked. The named downstream consumer is kernelNineteenAddHom_galois, followed by the actual cyclotomic character maps. This interface asserts no new character bound, Selmer finiteness or rational rank result.
-- source:
--   MazurTheorem Order13ActualNormKernelNineteenEmbedding, exact original constructors and structural laws; official Anthropic FLT interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the complete actual nineteen-killed norm kernel embeds
additively and Galois-equivariantly into the SAME Picard nineteen torsion.
Named downstream consumer: actual cyclotomic quotient maps via the pairing.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelF19RepresentationOriginalContextDataV220261018
import Definitions.Def_MazurTransfer_Order13ActualArithmeticNineteenTorsionGaloisHomOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionNormRestrictionOriginalData20261018

noncomputable section
namespace MazurTransfer.Order13ActualNormKernelNineteenEmbedding
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance kernelNineteenEmbeddingOriginalGroupProvider20261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance kernelNineteenEmbeddingOriginalCommProvider20261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance kernelNineteenEmbeddingOriginalPiHomProvider20261018 : IsMonHom schemePi := schemePi_isMonHom
local instance kernelNineteenEmbeddingOriginalConjugateHomProvider20261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance kernelNineteenEmbeddingOriginalActionProvider20261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ


open Order13ActualPicardNormAlgebraicCohomology


open Order13ActualNormKernelFiniteModule
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance kernelNineteenEmbeddingOriginalFiniteProvider20261018 : Finite (Kernel K φ) := kernel_finite K φ
local instance kernelNineteenEmbeddingOriginalModuleProvider20261018 : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ


open Order13ActualNormKernelProductCardinality
open Order13ActualNineteenTorsionNormPairingAdjoint
open Order13ActualNineteenTorsionGaloisPairingBridge
variable [IsAlgClosed K]

def kernelNineteenAddHom : Additive (Kernel K φ) →+ NineteenTorsion K where
  toFun z := ⟨Additive.ofMul z.toMul.val, by
    change z.toMul.val ^ 19 = 1
    exact congrArg Subtype.val ((Fact.out : ∀ w : Kernel K φ, w ^ 19 = 1) z.toMul)⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

theorem kernelNineteenAddHom_injective : Function.Injective (kernelNineteenAddHom K φ) := by
  intro x y h
  apply Additive.toMul.injective
  apply Subtype.ext
  exact congrArg (fun z : NineteenTorsion K => z.val.toMul) h

theorem kernelNineteenAddHom_norm_zero (z : Additive (Kernel K φ)) :
    actualNineteenTorsionNormHom K φ (kernelNineteenAddHom K φ z) = 0 := by
  apply Subtype.ext
  exact z.toMul.property

def kernelRestrictedAddHom : Additive (Kernel K φ) →+ (actualNineteenTorsionNormHom K φ).ker :=
  (kernelNineteenAddHom K φ).codRestrict _ (kernelNineteenAddHom_norm_zero K φ)

theorem kernelRestrictedAddHom_surjective : Function.Surjective (kernelRestrictedAddHom K φ) := by
  intro z
  have hz : normHom K φ z.val.val.toMul = 1 := congrArg (fun x : NineteenTorsion K => x.val.toMul) z.property
  refine ⟨Additive.ofMul ⟨z.val.val.toMul, hz⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  rfl

def kernelRestrictedAddEquiv : Additive (Kernel K φ) ≃+ (actualNineteenTorsionNormHom K φ).ker :=
  AddEquiv.ofBijective (kernelRestrictedAddHom K φ)
    ⟨fun x y h => kernelNineteenAddHom_injective K φ (congrArg Subtype.val h),
      kernelRestrictedAddHom_surjective K φ⟩

end MazurTransfer.Order13ActualNormKernelNineteenEmbedding
#print axioms MazurTransfer.Order13ActualNormKernelNineteenEmbedding.kernelNineteenAddHom
#print axioms MazurTransfer.Order13ActualNormKernelNineteenEmbedding.kernelRestrictedAddEquiv


