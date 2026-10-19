-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardAlgebraicNormQuotientKummerData
-- name    : MazurTransfer_Order13ActualPicardAlgebraicNormQuotientKummerData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T22:52:19.368319+00:00
-- url     : https://prove2.me/theorems/435a6d7c-0758-45ba-9b3a-272cdf4b769e
-- title:
--   Original actual rational norm quotient, chosen lift classes and algebraic Kummer quotient map
-- statement:
--   Let P be the same actual rational Picard group scheme, K a Galois extension of Q of characteristic zero, and phi an internal group endomorphism whose K-point map is surjective. Retain the original rational norm homomorphism, rational quotient, chosen preimage and cohomology-class constructions, and the well-defined quotient-class map $$P(\mathbb Q)/\varphi(P(\mathbb Q))\longrightarrow H^1(\operatorname{Aut}_{\mathbb Q}(K),\ker\varphi(K)).$$ The original division, choice-independence and constructor laws are packaged to support these definitions; the class-equality criterion is a proved dependency. Injectivity is a separate theorem. The named downstream consumers are the original quotientMap_injective and norm Kummer group homomorphism.
-- source:
--   Original MazurTheorem Order13ActualPicardNormAlgebraicKummerInjection eleven declarations through quotientMap, excluding the separately proved class-equality theorem and the subsequent injectivity theorem. Five original non-proof constructor values and all eleven full types are compared, with complete original group/action providers and H1 dependencies. Packaged structural facts receive no extra owned theorem credit. Apache-2.0. Design boundary: actual rational norm quotient and its original algebraic H1 quotient-class map. Named consumers: quotientMap_injective and Order13ActualPicardNormKummerGroupHom.chosenClass_div.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the rational quotient by an actual norm map injects
into Mathlib algebraic H1 of its actual geometric norm kernel.
Continuity and local conditions are separate obligations.
Named downstream consumer: continuous Kummer and Selmer bounds.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardNormAlgebraicCohomologyData
import Definitions.Def_MazurTransfer_Order13ActualPicardRationalFixedPointGroupData
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormAlgebraicKummerInjection_classOfLift_eq_iff_rational_norm_difference

noncomputable section
namespace MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormAlgebraicQuotientKummerDataProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormAlgebraicQuotientKummerDataProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormAlgebraicQuotientKummerDataProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormAlgebraicQuotientKummerDataProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
open Order13ActualPicardNormAlgebraicCohomology
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance actualNormAlgebraicQuotientKummerDataProvider520261017 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

def rationalNormHom : RationalPoints →* RationalPoints := IsMonHom.monoidHom φ _

theorem lift_div (a a' : RationalPoints) (b b' : Points K)
    (hb : b ≫ φ = rationalPoint K a) (hb' : b' ≫ φ = rationalPoint K a') :
    (b / b') ≫ φ = rationalPoint K (a / a') := by
  change normHom K φ (b / b') = rationalPointHom K (a / a')
  calc
    normHom K φ (b / b') = normHom K φ b / normHom K φ b' := map_div _ _ _
    _ = rationalPointHom K a / rationalPointHom K a' := congrArg₂ (fun x y => x / y) hb hb'
    _ = rationalPointHom K (a / a') := (map_div _ _ _).symm

theorem cocycle_div (a a' : RationalPoints) (b b' : Points K)
    (hb : b ≫ φ = rationalPoint K a) (hb' : b' ≫ φ = rationalPoint K a') :
    cocycle K φ (a / a') (b / b') (lift_div K φ a a' b b' hb hb') =
      cocycle K φ a b hb - cocycle K φ a' b' hb' := by
  apply Subtype.ext
  funext σ
  apply Subtype.ext
  change difference K (b / b') σ = difference K b σ / difference K b' σ
  simp [difference, EquivariantNormPreimageCocycle.difference, div_eq_mul_inv,
    map_mul, map_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]

theorem classOfLift_div (a a' : RationalPoints) (b b' : Points K)
    (hb : b ≫ φ = rationalPoint K a) (hb' : b' ≫ φ = rationalPoint K a') :
    classOfLift K φ (a / a') (b / b') (lift_div K φ a a' b b' hb hb') =
      classOfLift K φ a b hb - classOfLift K φ a' b' hb' := by
  rw [classOfLift, cocycle_div, map_sub]
  rfl

theorem classOfLift_independent (a : RationalPoints) (b b' : Points K)
    (hb : b ≫ φ = rationalPoint K a) (hb' : b' ≫ φ = rationalPoint K a) :
    classOfLift K φ a b hb = classOfLift K φ a b' hb' := by
  apply (classOfLift_eq_iff_rational_norm_difference K φ a a b b' hb hb').mpr
  refine ⟨1, ?_⟩
  rw [MonObj.one_comp]
  simp only [div_eq_mul_inv, mul_inv_cancel]

variable (hsurj : Function.Surjective (normHom K φ))

def chosenLift (a : RationalPoints) : Points K := Classical.choose (hsurj (rationalPoint K a))

theorem chosenLift_spec (a : RationalPoints) : chosenLift K φ hsurj a ≫ φ = rationalPoint K a :=
  Classical.choose_spec (hsurj (rationalPoint K a))

def chosenClass (a : RationalPoints) : groupCohomology.H1 (kernelRep K φ) :=
  classOfLift K φ a (chosenLift K φ hsurj a) (chosenLift_spec K φ hsurj a)

theorem chosenClass_eq_iff (a a' : RationalPoints) :
    chosenClass K φ hsurj a = chosenClass K φ hsurj a' ↔
      ∃ c : RationalPoints, c ≫ φ = a / a' :=
  classOfLift_eq_iff_rational_norm_difference K φ a a' _ _ _ _

abbrev NormQuotient := RationalPoints ⧸ (rationalNormHom φ).range

def quotientMap : NormQuotient φ → groupCohomology.H1 (kernelRep K φ) :=
  Quotient.lift (chosenClass K φ hsurj) (by
    intro a a' h
    apply (chosenClass_eq_iff K φ hsurj a a').mpr
    have heq : (a : NormQuotient φ) = a' := Quotient.sound h
    have hmem : a / a' ∈ (rationalNormHom φ).range := QuotientGroup.eq_iff_div_mem.mp heq
    exact hmem)

end MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection
#print axioms MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection.rationalNormHom
#print axioms MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection.lift_div
#print axioms MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection.cocycle_div
#print axioms MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection.classOfLift_div
#print axioms MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection.classOfLift_independent
#print axioms MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection.chosenLift
#print axioms MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection.chosenLift_spec
#print axioms MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection.chosenClass
#print axioms MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection.chosenClass_eq_iff
#print axioms MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection.NormQuotient
#print axioms MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection.quotientMap


