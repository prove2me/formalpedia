-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionLift
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_ReductionLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:30:33.393853+00:00
-- url     : https://prove2.me/theorems/ae1116bc-fa05-4eb5-b555-f46d5af4cfd4
-- title:
--   Reduction Lift
-- statement:
--   Definitions and structural lemmas for Reduction Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ReductionLift.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionGauss
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some


set_option autoImplicit false
namespace GroundTheory.Global
noncomputable section
open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate
variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (W : WeierstrassCurve 𝒪)
  {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] (j : 𝒪 →+* Λ) [IsLocalHom j]
  {x y : Λ} (hxy : (W.map j).toAffine.Equation x y)
omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsDomain Λ] [IsDiscreteValuationRing Λ]
  [IsLocalHom j] in
include hxy in
theorem eval₂_polynomial_of_equation :
    W.toAffine.polynomial.eval₂ (eval₂RingHom j x) y = 0 := by
  have e := (equation_iff _ _).mp hxy
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
  simp only [WeierstrassCurve.Affine.polynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
    coe_eval₂RingHom]
  linear_combination e
def coordEval : W.toAffine.CoordinateRing →+* Λ :=
  AdjoinRoot.lift (eval₂RingHom j x) y (eval₂_polynomial_of_equation W j hxy)
include hxy in

theorem equation_residue_of_equation :
    ((W.map (residue 𝒪)).map (ResidueField.map j)).toAffine.Equation (residue Λ x)
      (residue Λ y) := by
  have e := (equation_iff _ _).mp hxy
  rw [equation_iff]
  have := congrArg (residue Λ) e
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_add, map_mul, map_pow] at this ⊢
  simp only [← RingHom.comp_apply (ResidueField.map j), ResidueField.map_comp_residue]
  simpa only [RingHom.comp_apply] using this
include hxy in

def coordEvalRed :
    (W.map (residue 𝒪)).toAffine.CoordinateRing →+* ResidueField Λ :=
  AdjoinRoot.lift (eval₂RingHom (ResidueField.map j) (residue Λ x)) (residue Λ y)
    (eval₂_polynomial_of_equation (W.map (residue 𝒪)) (ResidueField.map j)
      (equation_residue_of_equation W j hxy))
theorem coordReduce_of (q : 𝒪[X]) :
    coordReduce W (AdjoinRoot.of _ q) = AdjoinRoot.of _ (q.map (residue 𝒪)) := by
  rw [← AdjoinRoot.mk_C, coordReduce, CoordinateRing.map_mk, Polynomial.map_C, ← AdjoinRoot.mk_C]
  rfl
theorem coordReduce_root :
    coordReduce W (AdjoinRoot.root W.toAffine.polynomial) =
      AdjoinRoot.root (W.map (residue 𝒪)).toAffine.polynomial := by
  rw [← AdjoinRoot.mk_X, coordReduce, CoordinateRing.map_mk, Polynomial.map_X, AdjoinRoot.mk_X]
theorem residue_coordEval (a : W.toAffine.CoordinateRing) :
    residue Λ (coordEval W j hxy a) = coordEvalRed W j hxy (coordReduce W a) := by
  have : (residue Λ).comp (coordEval W j hxy) = (coordEvalRed W j hxy).comp (coordReduce W) := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, coordReduce_of, coordEval, coordEvalRed, AdjoinRoot.lift_of,
          Polynomial.map_C, coe_eval₂RingHom, eval₂_C, ResidueField.map_residue]
      · simp only [RingHom.comp_apply, coordReduce_of, coordEval, coordEvalRed, AdjoinRoot.lift_of,
          Polynomial.map_X, coe_eval₂RingHom, eval₂_X]
    · simp only [RingHom.comp_apply, coordReduce_root, coordEval, coordEvalRed,
        AdjoinRoot.lift_root]
  exact congrArg (· a) this
variable (hx : Function.Injective (eval₂RingHom (ResidueField.map j) (residue Λ x)))
include hx in

theorem coordEvalRed_injective : Function.Injective (coordEvalRed W j hxy) := by
  letI : Algebra (ResidueField 𝒪) (ResidueField Λ) := (ResidueField.map j).toAlgebra
  have h : ((W.map (residue 𝒪)).baseChange (ResidueField Λ)).toAffine.Equation (residue Λ x)
      (residue Λ y) := equation_residue_of_equation W j hxy
  have ht : Transcendental (ResidueField 𝒪) (residue Λ x) := transcendental_iff_injective.mpr hx
  exact evalAt_injective (W.map (residue 𝒪)) h ht
include hx in
theorem isUnit_coordEval (s : (gaussPrime W).primeCompl) : IsUnit (coordEval W j hxy s) := by
  by_contra hs
  have h0 : residue Λ (coordEval W j hxy s) = 0 :=
    (residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 hs)
  rw [residue_coordEval] at h0
  exact s.2 (RingHom.mem_ker.2 ((map_eq_zero_iff _ (coordEvalRed_injective W j hxy hx)).1 h0))
def gaussLift : gaussRing W →+* Λ :=
  IsLocalization.lift (M := (gaussPrime W).primeCompl) (S := gaussRing W)
    (isUnit_coordEval W j hxy hx)
theorem gaussLift_algebraMap (a : W.toAffine.CoordinateRing) :
    gaussLift W j hxy hx (algebraMap _ _ a) = coordEval W j hxy a :=
  IsLocalization.lift_eq _ _
instance isLocalHom_gaussLift : IsLocalHom (gaussLift W j hxy hx) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (gaussPrime W).primeCompl a
  dsimp only at ha ⊢
  have hspec := IsLocalization.mk'_spec (gaussRing W) r s
  have hr : IsUnit (coordEval W j hxy r) := by
    have := congrArg (gaussLift W j hxy hx) hspec
    rw [map_mul, gaussLift_algebraMap, gaussLift_algebraMap] at this
    rw [← this]
    exact ha.mul (isUnit_coordEval W j hxy hx s)
  have hr' : r ∈ (gaussPrime W).primeCompl := by
    intro hP
    have h0 : coordReduce W r = 0 := hP
    have h1 : residue Λ (coordEval W j hxy r) = 0 := by rw [residue_coordEval, h0, map_zero]
    exact (residue_ne_zero_iff_isUnit _).2 hr h1
  have hu : IsUnit (IsLocalization.mk' (gaussRing W) r s *
      algebraMap W.toAffine.CoordinateRing (gaussRing W) (s : W.toAffine.CoordinateRing)) := by
    rw [hspec]; exact IsLocalization.map_units _ ⟨r, hr'⟩
  exact isUnit_of_mul_isUnit_left hu
def fieldEvalRed : (W.map (residue 𝒪)).toAffine.FunctionField →+* ResidueField Λ :=
  IsFractionRing.lift (coordEvalRed_injective W j hxy hx)
section Fraction
variable (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (M : Type*) [Field M]
  [Algebra Λ M]
end Fraction
end
end GroundTheory.Global


