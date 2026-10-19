-- Prove2me | Definitions.Def_MazurTransfer_Order13KernelActionFixedSubgroupOriginalDataAndCertificates20261018
-- name    : MazurTransfer_Order13KernelActionFixedSubgroupOriginalDataAndCertificates20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T20:07:19.402592+00:00
-- url     : https://prove2.me/theorems/3bd1c76b-8bb9-42eb-92cd-c36552b58f89
-- title:
--   Fixed norm kernels as fixed subgroups of the geometric kernel action
-- statement:
--   The original fixed subgroup of geometric points identifies with the fixed subgroup inside the geometric norm kernel. Both original constructor types and values, the cardinality certificate, three own provider types and two values, and four dependency provider types and three values are checked. Named downstream consumers: actual fixed kernel cardinalities and invariant dimensions.
-- source:
--   MazurTheorem original actual norm-kernel fixed-subgroup and invariant-dimension interfaces; complete original types and values retained; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify fixed geometric Picard kernel points with the
fixed subgroup of the actual kernel-valued Galois action used by Kummer.
Named downstream consumer: Order13ActualNormKernelFixedPartIdentification.
-/
import Definitions.Def_MazurTransfer_Order13RationalNormFixedKernelEquivalenceOriginalDataAndCertificatesExplicitRationalPointChangeV220261018
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKernelGaloisActionData

noncomputable section
namespace MazurTransfer.Order13ActualKernelActionFixedSubgroup
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles Order13ActualPicardGaloisFixedPointDescent
open Order13ActualPicardNormKernelGaloisAction Order13ActualNormFixedKernelEquivalence
open scoped CategoryTheory.MonObj
local instance kernelActionFixedOriginalGroupProvider20261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
local instance kernelActionFixedOriginalCommutativeProvider20261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).isCommMonObj
variable (K : Type) [Field K] [CharZero K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance kernelActionFixedOriginalActionProvider20261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

def kernelGaloisFixed : Subgroup (Kernel K φ) where
  carrier := {z | ∀ σ : K ≃ₐ[ℚ] K, σ • z = z}
  one_mem' σ := smul_one σ
  mul_mem' hz hw σ := by rw [smul_mul', hz σ, hw σ]
  inv_mem' hz σ := by rw [smul_inv', hz σ]

def fixedKernelSubtypeEquiv : fixedNormKernel K φ ≃* kernelGaloisFixed K φ where
  toFun z := ⟨⟨z.val, z.property.2⟩, fun σ => Subtype.ext (z.property.1 σ)⟩
  invFun z := ⟨z.val.val, ⟨fun σ => congrArg Subtype.val (z.property σ), z.val.property⟩⟩
  left_inv z := Subtype.ext rfl
  right_inv z := Subtype.ext (Subtype.ext rfl)
  map_mul' z w := Subtype.ext (Subtype.ext rfl)

theorem kernelGaloisFixed_card : Nat.card (kernelGaloisFixed K φ) = Nat.card (fixedNormKernel K φ) :=
  (Nat.card_congr (fixedKernelSubtypeEquiv K φ).toEquiv).symm

end MazurTransfer.Order13ActualKernelActionFixedSubgroup
#print axioms MazurTransfer.Order13ActualKernelActionFixedSubgroup.fixedKernelSubtypeEquiv
#print axioms MazurTransfer.Order13ActualKernelActionFixedSubgroup.kernelGaloisFixed_card


