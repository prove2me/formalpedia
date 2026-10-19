-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardNormKernelGaloisActionData
-- name    : MazurTransfer_Order13ActualPicardNormKernelGaloisActionData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T22:13:25.090757+00:00
-- url     : https://prove2.me/theorems/4e094086-d548-45bd-b4e1-9a93108ec585
-- title:
--   The original actual norm-kernel Galois action and kernel-valued preimage cocycle
-- statement:
--   Let P be the same actual rational Picard group scheme, K a characteristic-zero field, and phi an internal monoid endomorphism. Its geometric kernel is preserved by every Q-automorphism of K. Retain the original kernel subgroup, the distributive field-automorphism action, and the preimage-difference function valued in that kernel. The two immediate cocycle constructor laws and the original generic group calculations supporting these constructors are packaged with their full original types. All three constructor values, the original group provider and the original kernel-action provider are compared, including the dependency group provider. The named downstream consumers are actual norm algebraic cohomology, continuous cocycles and finite Galois kernel modules. Packaged structural facts receive no extra owned theorem credit.
-- source:
--   Original MazurTheorem Order13ActualPicardNormKernelGaloisAction three constructors and two immediate constructor laws, with original generic and actual Kummer structural calculations. Apache-2.0. Design boundary: actual norm-kernel Galois action and kernel-valued cocycle data. Named downstream consumers: Order13ActualPicardNormAlgebraicCohomology, continuous norm cocycles and finite norm-kernel modules.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: field automorphisms act on the actual geometric norm
kernel groups, and the preimage difference is a cocycle valued in that
kernel group. Continuity remains a separate obligation.
Named downstream consumer: continuous norm Kummer classes.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKummerData
noncomputable section
namespace MazurTransfer.KernelGaloisDataGenericHelpers20261017
open MazurTransfer.EquivariantNormPreimageCocycle
variable {G H : Type*} [Group G] [CommGroup H]
variable (ρ : G → H →* H) (f : H →* H)
theorem difference_in_kernel (heq : ∀ σ x, f (ρ σ x) = ρ σ (f x))
    {a b : H} (hb : f b = a) (ha : ∀ σ, ρ σ a = a) (σ : G) :
    f (difference ρ b σ) = 1 := by
  simp only [difference, map_mul, map_inv, heq, hb, ha, mul_inv_cancel]

theorem difference_cocycle (hmul : ∀ σ τ x, ρ (σ * τ) x = ρ σ (ρ τ x))
    (b : H) (σ τ : G) :
    difference ρ b (σ * τ) = difference ρ b σ * ρ σ (difference ρ b τ) := by
  simp only [difference, hmul, map_mul, map_inv]
  simp [mul_assoc, mul_left_comm, mul_comm]

theorem difference_one (hone : ∀ x, ρ 1 x = x) (b : H) :
    difference ρ b 1 = 1 := by
  simp only [difference, hone, mul_inv_cancel]

theorem kernel_preserved (heq : ∀ σ x, f (ρ σ x) = ρ σ (f x))
    {z : H} (hz : f z = 1) (σ : G) : f (ρ σ z) = 1 := by
  rw [heq, hz, map_one]
end MazurTransfer.KernelGaloisDataGenericHelpers20261017
namespace MazurTransfer.KernelGaloisDataKummerHelpers20261017
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open scoped CategoryTheory.MonObj
local instance kernelGaloisDataKummerProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance kernelGaloisDataKummerProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance kernelGaloisDataKummerProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance kernelGaloisDataKummerProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open MazurTransfer.Order13ActualPicardNormKummerCocycles
variable (K : Type) [Field K] [CharZero K]
theorem difference_in_kernel
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a)
    (σ : K ≃ₐ[ℚ] K) : difference K b σ ≫ φ = 1 :=
  MazurTransfer.KernelGaloisDataGenericHelpers20261017.difference_in_kernel (actionHom K) (normHom K φ)
    (fun σ x => (FieldAutomorphismOverPointAction.act_comp actualPicard.toBase σ x φ).symm)
    hb (fun σ => FieldAutomorphismOverPointAction.rationalPoint_fixed actualPicard.toBase σ a) σ

theorem difference_cocycle (b : Points K) (σ τ : K ≃ₐ[ℚ] K) :
    difference K b (σ * τ) = difference K b σ * actionHom K σ (difference K b τ) :=
  MazurTransfer.KernelGaloisDataGenericHelpers20261017.difference_cocycle (actionHom K)
    (fun σ τ x => FieldAutomorphismOverPointAction.act_mul actualPicard.toBase σ τ x) b σ τ

theorem difference_one (b : Points K) : difference K b 1 = 1 :=
  MazurTransfer.KernelGaloisDataGenericHelpers20261017.difference_one (actionHom K)
    (fun x => FieldAutomorphismOverPointAction.act_one actualPicard.toBase x) b
end MazurTransfer.KernelGaloisDataKummerHelpers20261017
namespace MazurTransfer.Order13ActualPicardNormKernelGaloisAction
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormKernelGaloisDataProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormKernelGaloisDataProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormKernelGaloisDataProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormKernelGaloisDataProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

variable (K : Type) [Field K] [CharZero K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]

abbrev Kernel := (normHom K φ).ker

abbrev kernelAction : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) where
  smul σ z := ⟨actionHom K σ z.val,
    MazurTransfer.KernelGaloisDataGenericHelpers20261017.kernel_preserved (actionHom K) (normHom K φ)
      (fun σ x => (FieldAutomorphismOverPointAction.act_comp actualPicard.toBase σ x φ).symm)
      z.property σ⟩
  one_smul z := by
    apply Subtype.ext
    change actionHom K 1 z.val = z.val
    exact FieldAutomorphismOverPointAction.act_one actualPicard.toBase z.val
  mul_smul σ τ z := by
    apply Subtype.ext
    change actionHom K (σ * τ) z.val = actionHom K σ (actionHom K τ z.val)
    exact FieldAutomorphismOverPointAction.act_mul actualPicard.toBase σ τ z.val
  smul_one σ := Subtype.ext (map_one (actionHom K σ))
  smul_mul σ z w := Subtype.ext (map_mul (actionHom K σ) z.val w.val)

local instance actualNormKernelGaloisDataProvider520261017 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

def kernelCocycle (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a)
    (σ : K ≃ₐ[ℚ] K) : Kernel K φ :=
  ⟨difference K b σ, MazurTransfer.KernelGaloisDataKummerHelpers20261017.difference_in_kernel K φ a b hb σ⟩

theorem kernelCocycle_law (a : RationalPoints) (b : Points K)
    (hb : b ≫ φ = rationalPoint K a) (σ τ : K ≃ₐ[ℚ] K) :
    kernelCocycle K φ a b hb (σ * τ) =
      kernelCocycle K φ a b hb σ * σ • kernelCocycle K φ a b hb τ := by
  apply Subtype.ext
  change difference K b (σ * τ) = difference K b σ * actionHom K σ (difference K b τ)
  exact MazurTransfer.KernelGaloisDataKummerHelpers20261017.difference_cocycle K b σ τ

theorem kernelCocycle_one (a : RationalPoints) (b : Points K)
    (hb : b ≫ φ = rationalPoint K a) : kernelCocycle K φ a b hb 1 = 1 := by
  apply Subtype.ext
  exact MazurTransfer.KernelGaloisDataKummerHelpers20261017.difference_one K b

end MazurTransfer.Order13ActualPicardNormKernelGaloisAction
#print axioms MazurTransfer.Order13ActualPicardNormKernelGaloisAction.Kernel
#print axioms MazurTransfer.Order13ActualPicardNormKernelGaloisAction.kernelAction
#print axioms MazurTransfer.Order13ActualPicardNormKernelGaloisAction.kernelCocycle
#print axioms MazurTransfer.Order13ActualPicardNormKernelGaloisAction.kernelCocycle_law
#print axioms MazurTransfer.Order13ActualPicardNormKernelGaloisAction.kernelCocycle_one


