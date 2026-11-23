-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionGauss
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_ReductionGauss
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:24.776182+00:00
-- url     : https://prove2.me/theorems/b6195c56-bff2-47cf-a1f5-ec7a7828c01c
-- title:
--   Reduction Gauss
-- statement:
--   Definitions and structural lemmas for Reduction Gauss, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ReductionGauss.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
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
variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (W : WeierstrassCurve 𝒪)
abbrev coordReduce :
    W.toAffine.CoordinateRing →+* (W.map (residue 𝒪)).toAffine.CoordinateRing :=
  CoordinateRing.map W (residue 𝒪)
theorem coordReduce_algebraMap (a : 𝒪) :
    coordReduce W (algebraMap 𝒪 W.toAffine.CoordinateRing a) =
      algebraMap (ResidueField 𝒪) _ (residue 𝒪 a) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    ← algebraMap_smul (A := 𝒪[X]) a (1 : W.toAffine.CoordinateRing), CoordinateRing.map_smul,
    map_one, ← algebraMap_smul (A := (ResidueField 𝒪)[X]) (residue 𝒪 a)]
  simp
omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in

theorem smul_basis_mul (c : 𝒪) (p q : 𝒪[X]) :
    (C c * p) • (1 : W.toAffine.CoordinateRing) + (C c * q) • CoordinateRing.mk W Y =
      algebraMap 𝒪 W.toAffine.CoordinateRing c * (p • 1 + q • CoordinateRing.mk W Y) := by
  rw [mul_add, mul_smul, mul_smul, ← Polynomial.algebraMap_eq, algebraMap_smul,
    algebraMap_smul]
  simp only [Algebra.smul_def]
def gaussPrime : Ideal W.toAffine.CoordinateRing := RingHom.ker (coordReduce W)
instance : (gaussPrime W).IsPrime := RingHom.ker_isPrime _
theorem gaussPrime_eq {ϖ : 𝒪} (hϖ : Irreducible ϖ) :
    gaussPrime W = Ideal.span {algebraMap 𝒪 W.toAffine.CoordinateRing ϖ} := by
  have hm : RingHom.ker (residue 𝒪) = Ideal.span {ϖ} := by
    rw [ker_residue, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
  apply le_antisymm
  · intro y hy
    obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq y
    have hy' : coordReduce W (p • 1 + q • CoordinateRing.mk W Y) = 0 := hy
    simp_rw [map_add, CoordinateRing.map_smul, map_one, CoordinateRing.map_mk, Polynomial.map_X]
      at hy'
    obtain ⟨hp, hq⟩ := CoordinateRing.smul_basis_eq_zero hy'
    have hker : ∀ r : 𝒪[X], r.map (residue 𝒪) = 0 → ∃ r' : 𝒪[X], r = C ϖ * r' := by
      intro r hr
      have : r ∈ RingHom.ker (mapRingHom (residue 𝒪)) := hr
      rw [Polynomial.ker_mapRingHom, hm, Ideal.map_span, Set.image_singleton,
        Ideal.mem_span_singleton'] at this
      obtain ⟨r', hr'⟩ := this
      exact ⟨r', by rw [← hr', mul_comm]⟩
    obtain ⟨p', rfl⟩ := hker p hp
    obtain ⟨q', rfl⟩ := hker q hq
    rw [smul_basis_mul, mul_comm]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show coordReduce W _ = 0
    rw [coordReduce_algebraMap, (residue_eq_zero_iff _).2, map_zero]
    exact (mem_maximalIdeal _).2 hϖ.not_isUnit
abbrev gaussRing : Type _ := Localization.AtPrime (gaussPrime W)
omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
theorem algebraMap_coordinateRing_injective :
    Function.Injective (algebraMap 𝒪 W.toAffine.CoordinateRing) :=
  FaithfulSMul.algebraMap_injective _ _
theorem algebraMap_gaussRing_injective :
    Function.Injective (algebraMap W.toAffine.CoordinateRing (gaussRing W)) :=
  IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors (gaussPrime W))
instance : IsDiscreteValuationRing (gaussRing W) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  have hmax : maximalIdeal (gaussRing W) = Ideal.span {algebraMap W.toAffine.CoordinateRing
      (gaussRing W) (algebraMap 𝒪 W.toAffine.CoordinateRing ϖ)} := by
    have e := congrArg (Ideal.map (algebraMap W.toAffine.CoordinateRing (gaussRing W)))
      (gaussPrime_eq W hϖ)
    refine (Localization.AtPrime.map_eq_maximalIdeal (I := gaussPrime W)).symm.trans ?_
    rw [e, Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField (gaussRing W) := by
    rw [isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
    exact (map_ne_zero_iff _ (algebraMap_gaussRing_injective W)).2
      ((map_ne_zero_iff _ (algebraMap_coordinateRing_injective W)).2 hϖ.ne_zero)
  refine ((IsDiscreteValuationRing.TFAE (gaussRing W) hnf).out 0 4).mpr ?_
  rw [hmax]
  exact ⟨⟨_, rfl⟩⟩
section Fraction
variable (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in

theorem coordinateRing_map_algebraMap {S : Type*} [CommRing S] (f : 𝒪 →+* S) (a : 𝒪) :
    CoordinateRing.map W f (algebraMap 𝒪 W.toAffine.CoordinateRing a) =
      algebraMap S (W.map f).toAffine.CoordinateRing (f a) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    ← algebraMap_smul (A := 𝒪[X]) a (1 : W.toAffine.CoordinateRing), CoordinateRing.map_smul,
    map_one, ← algebraMap_smul (A := S[X]) (f a)]
  simp
abbrev coordBase : W.toAffine.CoordinateRing →+* (W.baseChange K).toAffine.CoordinateRing :=
  CoordinateRing.map W (algebraMap 𝒪 K)
omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] in
theorem coordBase_algebraMap (a : 𝒪) :
    coordBase W K (algebraMap 𝒪 W.toAffine.CoordinateRing a) =
      algebraMap 𝒪 (W.baseChange K).toAffine.CoordinateRing a :=
  (coordinateRing_map_algebraMap W (algebraMap 𝒪 K) a).trans
    (IsScalarTower.algebraMap_apply 𝒪 K (W.baseChange K).toAffine.CoordinateRing a).symm
instance : Algebra W.toAffine.CoordinateRing (W.baseChange K).toAffine.FunctionField :=
  ((algebraMap (W.baseChange K).toAffine.CoordinateRing _).comp (coordBase W K)).toAlgebra
omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] in
theorem algebraMap_coordinateRing_functionField (a : W.toAffine.CoordinateRing) :
    algebraMap W.toAffine.CoordinateRing (W.baseChange K).toAffine.FunctionField a =
      algebraMap _ _ (coordBase W K a) :=
  rfl
omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
theorem algebraMap_coordinateRing_functionField_injective :
    Function.Injective
      (algebraMap W.toAffine.CoordinateRing (W.baseChange K).toAffine.FunctionField) := by
  intro a b h
  rw [algebraMap_coordinateRing_functionField, algebraMap_coordinateRing_functionField] at h
  exact CoordinateRing.map_injective (IsFractionRing.injective 𝒪 K)
    (IsFractionRing.injective (W.baseChange K).toAffine.CoordinateRing _ h)
theorem exists_map_eq_smul (α : (W.baseChange K).toAffine.CoordinateRing) :
    ∃ (c : 𝒪) (a : W.toAffine.CoordinateRing), c ≠ 0 ∧
      coordBase W K a = c • α := by
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq α
  obtain ⟨b, hb, hbp⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors 𝒪) p
  obtain ⟨b', hb', hbq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors 𝒪) q
  refine ⟨b * b', (b' • IsLocalization.integerNormalization (nonZeroDivisors 𝒪) p) • 1 +
    (b • IsLocalization.integerNormalization (nonZeroDivisors 𝒪) q) • CoordinateRing.mk W Y,
    mul_ne_zero (nonZeroDivisors.ne_zero hb) (nonZeroDivisors.ne_zero hb'), ?_⟩
  change CoordinateRing.map W (algebraMap 𝒪 K) _ = _
  rw [map_add, CoordinateRing.map_smul, CoordinateRing.map_smul, map_one, CoordinateRing.map_mk,
    Polynomial.map_X, Polynomial.map_smul, Polynomial.map_smul, hbp, hbq, smul_add]
  simp only [algebraMap_smul, smul_assoc, smul_smul, mul_comm b b']
  rfl
instance : IsFractionRing W.toAffine.CoordinateRing (W.baseChange K).toAffine.FunctionField := by
  have hinj := algebraMap_coordinateRing_functionField_injective W K
  refine (isLocalization_iff _ _).mpr ⟨fun y => ?_, fun z => ?_, fun {x y} h => ⟨1, by rw [hinj h]⟩⟩
  · exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero y.2))
  · obtain ⟨α, β, hβ, rfl⟩ :=
      IsFractionRing.div_surjective (A := (W.baseChange K).toAffine.CoordinateRing) z
    obtain ⟨c₁, a₁, hc₁, ha₁⟩ := exists_map_eq_smul W K α
    obtain ⟨c₂, a₂, hc₂, ha₂⟩ := exists_map_eq_smul W K β
    have hβ0 : algebraMap _ (W.baseChange K).toAffine.FunctionField β ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (nonZeroDivisors.ne_zero hβ)
    have hc : ∀ c : 𝒪, c ≠ 0 → algebraMap 𝒪 (W.baseChange K).toAffine.FunctionField c ≠ 0 :=
      fun c hc => by
        rw [IsScalarTower.algebraMap_apply 𝒪 K]
        exact (map_ne_zero_iff _ (algebraMap K _).injective).2
          ((map_ne_zero_iff _ (IsFractionRing.injective 𝒪 K)).2 hc)
    have key : ∀ (c : 𝒪) (a : W.toAffine.CoordinateRing),
        algebraMap W.toAffine.CoordinateRing (W.baseChange K).toAffine.FunctionField
          (algebraMap 𝒪 _ c * a) = algebraMap 𝒪 _ c *
            algebraMap W.toAffine.CoordinateRing (W.baseChange K).toAffine.FunctionField a := by
      intro c a
      rw [map_mul, algebraMap_coordinateRing_functionField W K (algebraMap 𝒪 _ c),
        coordBase_algebraMap, ← IsScalarTower.algebraMap_apply]
    have hs : algebraMap 𝒪 W.toAffine.CoordinateRing c₁ * a₂ ∈ nonZeroDivisors _ := by
      refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
      have := congrArg (algebraMap W.toAffine.CoordinateRing
        (W.baseChange K).toAffine.FunctionField) h0
      rw [key, map_zero, algebraMap_coordinateRing_functionField, ha₂, Algebra.smul_def,
        map_mul, ← IsScalarTower.algebraMap_apply] at this
      exact mul_ne_zero (hc c₁ hc₁) (mul_ne_zero (hc c₂ hc₂) hβ0) this
    refine ⟨⟨algebraMap 𝒪 _ c₂ * a₁, ⟨_, hs⟩⟩, ?_⟩
    simp only
    rw [key, key, algebraMap_coordinateRing_functionField, algebraMap_coordinateRing_functionField,
      ha₁, ha₂, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    field_simp
theorem isUnit_algebraMap_primeCompl (y : (gaussPrime W).primeCompl) :
    IsUnit (algebraMap W.toAffine.CoordinateRing (W.baseChange K).toAffine.FunctionField y) :=
  IsLocalization.map_units (W.baseChange K).toAffine.FunctionField
    (⟨y.1, Ideal.primeCompl_le_nonZeroDivisors (gaussPrime W) y.2⟩ :
      nonZeroDivisors W.toAffine.CoordinateRing)
instance : Algebra (gaussRing W) (W.baseChange K).toAffine.FunctionField :=
  (IsLocalization.lift (M := (gaussPrime W).primeCompl) (S := gaussRing W)
    (isUnit_algebraMap_primeCompl W K)).toAlgebra
instance : IsScalarTower W.toAffine.CoordinateRing (gaussRing W)
    (W.baseChange K).toAffine.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun a => (IsLocalization.lift_eq _ a).symm
instance : IsFractionRing (gaussRing W) (W.baseChange K).toAffine.FunctionField :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (gaussPrime W).primeCompl _ _
instance : IsScalarTower 𝒪 (gaussRing W) (W.baseChange K).toAffine.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply 𝒪 W.toAffine.CoordinateRing (gaussRing W),
      ← IsScalarTower.algebraMap_apply, algebraMap_coordinateRing_functionField,
      coordBase_algebraMap, ← IsScalarTower.algebraMap_apply]
end Fraction
section Residue
def gaussResidue : ResidueField (gaussRing W) →+* (W.map (residue 𝒪)).toAffine.FunctionField :=
  IsFractionRing.lift (A := W.toAffine.CoordinateRing ⧸ gaussPrime W)
    (K := (gaussPrime W).ResidueField)
    (g := (algebraMap _ (W.map (residue 𝒪)).toAffine.FunctionField).comp
      (RingHom.kerLift (coordReduce W)))
    ((IsFractionRing.injective _ _).comp (RingHom.kerLift_injective _))
end Residue
section Generators
variable (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
def gaussX : gaussRing W := algebraMap W.toAffine.CoordinateRing _ (CoordinateRing.mk W (C X))
def gaussY : gaussRing W := algebraMap W.toAffine.CoordinateRing _ (CoordinateRing.mk W Y)
end Generators
instance : IsLocalHom (algebraMap 𝒪 (gaussRing W)) := by
  refine ⟨fun c hc => ?_⟩
  by_contra h
  have hm : algebraMap 𝒪 (gaussRing W) c ∈ maximalIdeal (gaussRing W) := by
    rw [IsScalarTower.algebraMap_apply 𝒪 W.toAffine.CoordinateRing (gaussRing W),
      IsLocalization.AtPrime.to_map_mem_maximal_iff _ (gaussPrime W)]
    show coordReduce W _ = 0
    rw [coordReduce_algebraMap, (residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 h), map_zero]
  exact (mem_maximalIdeal _).1 hm hc
end
end GroundTheory.Global


