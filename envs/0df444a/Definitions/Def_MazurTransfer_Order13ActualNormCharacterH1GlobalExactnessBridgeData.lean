-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNormCharacterH1GlobalExactnessBridgeData
-- name    : MazurTransfer_Order13ActualNormCharacterH1GlobalExactnessBridgeData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T02:42:38.767004+00:00
-- url     : https://prove2.me/theorems/c0ab24c7-68ca-4217-8238-779a3bc3b9cc
-- title:
--   Middle H1 exactness for specified actual norm-character intertwiners
-- statement:
--   Let \(K/\mathbb Q\) be the original characteristic-zero Galois field, let \(\phi\) be a finite internal group endomorphism of the actual Picard object, and suppose its geometric kernel is killed by \(19\). Given the original representations \(\sigma,\tau\), an injective intertwiner \(i\) into the kernel representation and a surjective intertwiner \(p\) out of it with \(\operatorname{im}i=\ker p\), the induced continuous cohomology maps satisfy \[\operatorname{im} H^1(i)=\ker H^1(p).\] This specializes the verified coefficient exactness theorem to the specified maps. Named downstream consumer: the exact kernel criterion for the actual norm-character Kummer pushforward. This immediate bridge is packaged without an additional owned theorem acceptance.
-- source:
--   Original MazurTheorem constructor or immediate exactness interface, Apache-2.0; complete original types and nonproof values are compared.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an actual norm-character representation sequence is exact
at the EXISTING continuous H1 globally and after restriction to every subgroup.
Named downstream consumer: kernel control for actual norm Selmer images.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormCharacterH1ExactSequenceData
import Theorems.Thm_MazurTransfer_ContinuousFirstCohomologyExactSequence_range_eq_ker

/- Design boundary: middle-H1 exactness for the specified intertwiners.
Named downstream consumer: normQuotient_image_zero_iff_character_lift. -/
noncomputable section
namespace MazurTransfer.Order13ActualNormCharacterH1Exactness
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormCharacterH1GlobalExactnessBridgeProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormCharacterH1GlobalExactnessBridgeProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormCharacterH1GlobalExactnessBridgeProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormCharacterH1GlobalExactnessBridgeProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance actualNormCharacterH1GlobalExactnessBridgeProvider520261018 : TopologicalSpace (Points K) := pointsTopology K
local instance actualNormCharacterH1GlobalExactnessBridgeProvider620261018 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualNormCharacterH1GlobalExactnessBridgeProvider720261018 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualNormCharacterH1GlobalExactnessBridgeProvider820261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ



open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormSubgroupRestrictionF19
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance actualNormCharacterH1GlobalExactnessBridgeProvider920261018 : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ
local instance actualNormCharacterH1GlobalExactnessBridgeProvider1020261018 : Module (ZMod 19) (ContinuousH1 K φ) := globalH1ZModModule K φ
local instance actualNormCharacterH1GlobalExactnessBridgeProvider1120261018 : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ
open RepresentationDiscreteCoefficientInclusion
open Order13ActualNormCharacterContinuousH1
variable {U V : Type} [AddCommGroup U] [Module (ZMod 19) U]
  [AddCommGroup V] [Module (ZMod 19) V]
variable (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U)
  (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
variable (i : Representation.IntertwiningMap σ (kernelRepresentation K φ))
  (p : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
local instance actualNormCharacterH1GlobalExactnessBridgeProvider1220261018 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient σ)) :=
  coefficientH1ZModModule σ
local instance actualNormCharacterH1GlobalExactnessBridgeProvider1320261018 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient τ)) :=
  coefficientH1ZModModule τ


theorem range_inclusionClass_eq_ker_mapClass
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap) :
    LinearMap.range (inclusionClass K φ σ i) = LinearMap.ker (mapClass K φ τ p) := by
  ext x
  exact SetLike.ext_iff.mp (ContinuousFirstCohomologyExactSequence.range_eq_ker
    (K ≃ₐ[ℚ] K) (Coefficient σ) (Kernel K φ) (Coefficient τ)
    (toIntertwining σ (kernelRepresentation K φ) i)
    (fromIntertwining (kernelRepresentation K φ) τ p)
    (toIntertwining_equivariant σ (kernelRepresentation K φ) i (by intro g m; rfl))
    (fromIntertwining_equivariant (kernelRepresentation K φ) τ p (by intro g m; rfl))
    (toIntertwining_injective σ (kernelRepresentation K φ) i hi)
    (fromIntertwining_surjective (kernelRepresentation K φ) τ p hp)
    (coefficient_exact σ (kernelRepresentation K φ) τ i p hk)) x

end MazurTransfer.Order13ActualNormCharacterH1Exactness
#print axioms MazurTransfer.Order13ActualNormCharacterH1Exactness.range_inclusionClass_eq_ker_mapClass


