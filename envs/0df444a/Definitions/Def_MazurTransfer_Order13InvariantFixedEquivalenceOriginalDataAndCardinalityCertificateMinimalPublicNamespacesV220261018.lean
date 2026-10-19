-- Prove2me | Definitions.Def_MazurTransfer_Order13InvariantFixedEquivalenceOriginalDataAndCardinalityCertificateMinimalPublicNamespacesV220261018
-- name    : MazurTransfer_Order13InvariantFixedEquivalenceOriginalDataAndCardinalityCertificateMinimalPublicNamespacesV220261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T20:09:18.538972+00:00
-- url     : https://prove2.me/theorems/1f458246-a8c4-4c53-95d8-6729dd289751
-- title:
--   Original invariant-space fixed-kernel equivalence and cardinality formula
-- statement:
--   The invariants of the original F19 kernel representation are equivalent to the geometric kernel fixed subgroup. Its cardinality is nineteen raised to the invariant finrank. The original two complete declaration types and one whole constructor value are checked, with nine own provider types and three values and fourteen context provider types and eight values. Named downstream consumer: the exact dimensions zero and one of the actual norm-kernel invariant spaces.
-- source:
--   MazurTheorem original actual norm-kernel fixed-subgroup and invariant-dimension interfaces; complete original types and values retained; Apache-2.0.

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the invariant F19-subspaces of the two actual geometric
norm kernels have dimensions zero and one, using genuine rational
fixed-point descent and the exact nineteen torsion counts.
Named downstream consumer: actual kernel Galois module structure and Selmer bounds. -/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelF19RepresentationOriginalContextDataV220261018
import Definitions.Def_MazurTransfer_Order13KernelActionFixedSubgroupOriginalDataAndCertificates20261018

noncomputable section
namespace MazurTransfer.Order13ActualNormKernelInvariantDimensions
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance invariantFixedOriginalProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance invariantFixedOriginalProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance invariantFixedOriginalProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance invariantFixedOriginalProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance invariantFixedOriginalProvider520261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ


open Order13ActualPicardNormAlgebraicCohomology


open Order13ActualNormKernelFiniteModule
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance invariantFixedOriginalProvider620261018 : Finite (Kernel K φ) := kernel_finite K φ
local instance invariantFixedOriginalProvider720261018 : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ


open Order13ActualNormKernelF19Representation Order13ActualKernelActionFixedSubgroup
local instance invariantFixedOriginalProvider820261018 : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance invariantFixedOriginalProvider920261018 : Module.Finite (ZMod 19) (Additive (Kernel K φ)) := kernel_module_finite K φ

def invariantFixedEquiv : (kernelRepresentation K φ).invariants ≃ kernelGaloisFixed K φ where
  toFun z := ⟨z.val.toMul, fun σ => by
    have h := z.property σ
    change Additive.ofMul (σ • z.val.toMul) = Additive.ofMul z.val.toMul at h
    exact congrArg Additive.toMul h⟩
  invFun z := ⟨Additive.ofMul z.val, fun σ => congrArg Additive.ofMul (z.property σ)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem fixed_card_eq_pow_invariant_finrank :
    Nat.card (kernelGaloisFixed K φ) =
      19 ^ Module.finrank (ZMod 19) (kernelRepresentation K φ).invariants := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 19)
    (V := (kernelRepresentation K φ).invariants)
  rw [Nat.card_zmod] at h
  exact (Nat.card_congr (invariantFixedEquiv K φ)).symm.trans h

end MazurTransfer.Order13ActualNormKernelInvariantDimensions
#print axioms MazurTransfer.Order13ActualNormKernelInvariantDimensions.invariantFixedEquiv
#print axioms MazurTransfer.Order13ActualNormKernelInvariantDimensions.fixed_card_eq_pow_invariant_finrank


