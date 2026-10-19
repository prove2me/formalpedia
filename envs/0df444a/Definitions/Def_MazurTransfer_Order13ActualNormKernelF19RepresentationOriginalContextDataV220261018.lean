-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNormKernelF19RepresentationOriginalContextDataV220261018
-- name    : MazurTransfer_Order13ActualNormKernelF19RepresentationOriginalContextDataV220261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T01:25:47.384204+00:00
-- url     : https://prove2.me/theorems/dc8d4081-6d0d-45e1-bfae-ed8757b243a6
-- title:
--   Original F19 representation of an actual norm kernel and its pointwise kernel criterion
-- statement:
--   For the same actual rational Picard, a characteristic-zero extension field K, an internal group endomorphism phi and the original exponent-nineteen kernel fact, retain the original representation over ZMod 19 on the additive form of ker(phi)(K). Its original constructor type requires neither finiteness nor the Galois hypothesis. The original pointwise representation-kernel criterion retains its full Galois and finite-endomorphism context: an automorphism lies in the representation kernel exactly when it fixes every kernel point. Both complete original types and the one nonproof constructor value are compared. All three original group/action/module instance providers and the relevant Kummer, kernel-action, algebraic-H1 and finite-module dependencies are compared in full types and values. The criterion is a packaged computation fact, with no extra owned theorem acceptance. Named downstream consumers are the original open-kernel theorem and actual norm-character continuous H1 maps. No rank, splitting-field construction or good-prime inertia assertion is made.
-- source:
--   Original MazurTheorem Order13ActualNormKernelF19Representation.kernelRepresentation and representation_kernel_iff, Apache-2.0. Original declaration bodies and complete original contexts retained; an unused proof-only namespace opening is omitted in the corrected public-source variant.

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual finite norm kernel Galois action is F19-linear,
with open normal kernel and trivial good-prime valuation inertia.
Named downstream consumer: actual finite Galois splitting fields and Selmer bounds. -/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelFiniteF19ModuleWithOriginalExponentFactsData20261017
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelFiniteModule_kernel_finite
import Definitions.Def_MazurTransfer_Order13ActualPicardNormAlgebraicCohomologyData
import Mathlib.RepresentationTheory.Basic

/- This constructor interface retains the original finite kernel representation and
its pointwise kernel criterion. Its named consumers are the original open-kernel
theorem and the actual norm-character continuous H1 maps. -/
noncomputable section
namespace MazurTransfer.Order13ActualNormKernelF19Representation
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormKernelF19RepresentationDataV2Provider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormKernelF19RepresentationDataV2Provider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormKernelF19RepresentationDataV2Provider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormKernelF19RepresentationDataV2Provider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance actualNormKernelF19RepresentationDataV2Provider520261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ


open Order13ActualPicardNormAlgebraicCohomology


open Order13ActualNormKernelFiniteModule
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance actualNormKernelF19RepresentationDataV2Provider620261018 : Finite (Kernel K φ) := kernel_finite K φ
local instance actualNormKernelF19RepresentationDataV2Provider720261018 : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ

def kernelRepresentation : Representation (ZMod 19) (K ≃ₐ[ℚ] K) (Additive (Kernel K φ)) where
  toFun σ := (show Additive (Kernel K φ) →+ Additive (Kernel K φ) from
    ((kernelRep K φ).ρ σ).toAddMonoidHom).toZModLinearMap 19
  map_one' := by
    apply LinearMap.ext
    intro z
    exact LinearMap.congr_fun (map_one (kernelRep K φ).ρ) z
  map_mul' σ τ := by
    apply LinearMap.ext
    intro z
    exact LinearMap.congr_fun (map_mul (kernelRep K φ).ρ σ τ) z

theorem representation_kernel_iff (σ : K ≃ₐ[ℚ] K) :
    σ ∈ (kernelRepresentation K φ).ker ↔ ∀ z : Kernel K φ, σ • z = z := by
  constructor
  · intro h z
    have hlin : kernelRepresentation K φ σ = 1 := h
    have hz := LinearMap.congr_fun hlin (Additive.ofMul z)
    change Additive.ofMul (σ • z) = Additive.ofMul z at hz
    exact congrArg Additive.toMul hz
  · intro h
    apply LinearMap.ext
    intro z
    change Additive.ofMul (σ • z.toMul) = Additive.ofMul z.toMul
    exact congrArg Additive.ofMul (h z.toMul)

end MazurTransfer.Order13ActualNormKernelF19Representation
#print axioms MazurTransfer.Order13ActualNormKernelF19Representation.kernelRepresentation
#print axioms MazurTransfer.Order13ActualNormKernelF19Representation.representation_kernel_iff


