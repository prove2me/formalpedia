-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IrreducibleSpacePrimeSpectrumAway
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IrreducibleSpacePrimeSpectrumAway
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T12:54:22.276426+00:00
-- url     : https://prove2.me/theorems/0ca88a05-549b-4eec-88fc-4333ebdfa45d
-- title:
--   Irreducible Space Prime Spectrum Away
-- statement:
--   Definitions and structural lemmas for Irreducible Space Prime Spectrum Away, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IrreducibleSpacePrimeSpectrumAway.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
import Theorems.Thm_GlobalTheory_ChartRing_evalAdic_C
import Theorems.Thm_GlobalTheory_ChartRing_evalAdic_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ChartRing.evalAdic_C
attribute [local simp] GlobalTheory.ChartRing.evalAdic_X


set_option autoImplicit false
open PowerSeries
noncomputable section
namespace GlobalTheory.ChartRing
section PrimeX
variable {O : Type*} [CommRing O] [IsDomain O]
instance isPrime_span_X : (Ideal.span {X} : Ideal O⟦X⟧).IsPrime := span_X_isPrime
omit [IsDomain O] in
theorem mem_span_X_iff {f : O⟦X⟧} : f ∈ (Ideal.span {X} : Ideal O⟦X⟧) ↔ constantCoeff f = 0 := by
  rw [Ideal.mem_span_singleton, X_dvd_iff]
theorem mem_primeCompl_span_X_iff {f : O⟦X⟧} :
    f ∈ (Ideal.span {X} : Ideal O⟦X⟧).primeCompl ↔ constantCoeff f ≠ 0 :=
  mem_span_X_iff.not
variable (S : Type*) [CommRing S] [Algebra O⟦X⟧ S]
  [IsLocalization.AtPrime S (Ideal.span {X} : Ideal O⟦X⟧)]
include O in
theorem isDomain_atPrime_X : IsDomain S :=
  IsLocalization.isDomain_of_atPrime S (Ideal.span {X} : Ideal O⟦X⟧)
theorem algebraMap_injective_atPrime_X : Function.Injective (algebraMap O⟦X⟧ S) :=
  IsLocalization.injective S (Ideal.span {X} : Ideal O⟦X⟧).primeCompl_le_nonZeroDivisors
theorem isUnit_algebraMap_atPrime_X {f : O⟦X⟧} (hf : constantCoeff f ≠ 0) :
    IsUnit (algebraMap O⟦X⟧ S f) :=
  IsLocalization.map_units S (⟨f, mem_primeCompl_span_X_iff.2 hf⟩ :
    (Ideal.span {X} : Ideal O⟦X⟧).primeCompl)
theorem associated_X_pow_order_atPrime {f : O⟦X⟧} (hf : f ≠ 0) :
    Associated (algebraMap O⟦X⟧ S X ^ f.order.toNat) (algebraMap O⟦X⟧ S f) := by
  conv_rhs => rw [← X_pow_order_mul_divXPowOrder (f := f), map_mul, map_pow]
  exact associated_mul_unit_right _ _
    (isUnit_algebraMap_atPrime_X S (constantCoeff_divXPowOrder_eq_zero_iff.not.2 hf))
theorem prime_algebraMap_X_atPrime : Prime (algebraMap O⟦X⟧ S X) := by
  have hne : algebraMap O⟦X⟧ S X ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap_injective_atPrime_X S)).2 X_ne_zero
  rw [← Ideal.span_singleton_prime hne, ← Set.image_singleton, ← Ideal.map_span]
  exact IsLocalization.isPrime_of_isPrime_disjoint (Ideal.span {X} : Ideal O⟦X⟧).primeCompl S _
    inferInstance (Set.disjoint_left.2 fun _ h h' => h h')
theorem exists_associated_X_pow_atPrime {z : S} (hz : z ≠ 0) :
    ∃ n : ℕ, Associated (algebraMap O⟦X⟧ S X ^ n) z := by
  obtain ⟨⟨f, s⟩, hfs⟩ := IsLocalization.surj (Ideal.span {X} : Ideal O⟦X⟧).primeCompl z
  have hs := IsLocalization.map_units S s
  have hf : f ≠ 0 := by
    rintro rfl
    exact hz (hs.mul_left_eq_zero.1 (by simpa using hfs))
  refine ⟨_, (associated_X_pow_order_atPrime S hf).trans ?_⟩
  rw [← hfs]
  exact associated_mul_unit_left _ _ hs
include O in

theorem isDiscreteValuationRing_atPrime_X [IsDomain S] : IsDiscreteValuationRing S :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, (prime_algebraMap_X_atPrime (O := O) S).irreducible,
      fun hz => exists_associated_X_pow_atPrime S hz⟩
instance : IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {X} : Ideal O⟦X⟧)) :=
  isDiscreteValuationRing_atPrime_X (O := O) _
end PrimeX
section FractionField
variable {O : Type*} [CommRing O] [IsDomain O] (K : Type*) [Field K] [Algebra O K]
  [IsFractionRing O K]
theorem addVal_eq_order (f : K⟦X⟧) : IsDiscreteValuationRing.addVal K⟦X⟧ f = f.order := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hu : IsUnit (divXPowOrder f) := isUnit_iff_constantCoeff.2
    (isUnit_iff_ne_zero.2 (constantCoeff_divXPowOrder_eq_zero_iff.not.2 hf))
  rw [IsDiscreteValuationRing.addVal_def f hu.unit X_irreducible f.order.toNat
    (by rw [IsUnit.unit_spec, mul_comm, X_pow_order_mul_divXPowOrder]), coe_toNat_order hf]
theorem algebraMap_residueField_span_X (f : O⟦X⟧) :
    algebraMap O⟦X⟧ (Ideal.span {X} : Ideal O⟦X⟧).ResidueField f =
      algebraMap O (Ideal.span {X} : Ideal O⟦X⟧).ResidueField (constantCoeff f) := by
  rw [IsScalarTower.algebraMap_apply O O⟦X⟧, ← sub_eq_zero, ← map_sub,
    Ideal.algebraMap_residueField_eq_zero, mem_span_X_iff]
  simp [PowerSeries.algebraMap_apply]
instance isFractionRing_residueField_span_X :
    IsFractionRing O (Ideal.span {X} : Ideal O⟦X⟧).ResidueField := by
  have : FaithfulSMul O (Ideal.span {X} : Ideal O⟦X⟧).ResidueField := by
    rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
    intro a ha
    rw [IsScalarTower.algebraMap_apply O O⟦X⟧, Ideal.algebraMap_residueField_eq_zero,
      mem_span_X_iff] at ha
    simpa [PowerSeries.algebraMap_apply] using ha
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨x, y, -, rfl⟩ :=
    IsFractionRing.div_surjective (A := O⟦X⟧ ⧸ (Ideal.span {X} : Ideal O⟦X⟧)) z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨constantCoeff x, constantCoeff y, by
    rw [Ideal.algebraMap_quotient_residueField_mk, Ideal.algebraMap_quotient_residueField_mk,
      algebraMap_residueField_span_X, algebraMap_residueField_span_X]⟩
variable (O) in

def residueFieldSpanXEquiv : (Ideal.span {X} : Ideal O⟦X⟧).ResidueField ≃ₐ[O] K :=
  IsLocalization.algEquiv (nonZeroDivisors O) _ _
@[simp] theorem residueFieldSpanXEquiv_algebraMap (f : O⟦X⟧) :
    residueFieldSpanXEquiv O K (algebraMap O⟦X⟧ _ f) = algebraMap O K (constantCoeff f) := by
  rw [algebraMap_residueField_span_X, AlgEquiv.commutes]
variable (S : Type*) [CommRing S] [Algebra O⟦X⟧ S]
  [IsLocalization.AtPrime S (Ideal.span {X} : Ideal O⟦X⟧)]
variable (O) in

def atPrimeXToPowerSeries : S →+* K⟦X⟧ :=
  IsLocalization.lift (M := (Ideal.span {X} : Ideal O⟦X⟧).primeCompl)
    (g := PowerSeries.map (algebraMap O K)) fun y =>
      isUnit_iff_constantCoeff.2 <| isUnit_iff_ne_zero.2 <| by
        have := mem_primeCompl_span_X_iff.1 y.2
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]
        exact (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 this
@[simp] theorem atPrimeXToPowerSeries_algebraMap (f : O⟦X⟧) :
    atPrimeXToPowerSeries O K S (algebraMap O⟦X⟧ S f) = f.map (algebraMap O K) :=
  IsLocalization.lift_eq _ _
theorem order_atPrimeXToPowerSeries [IsDomain S] [IsDiscreteValuationRing S] (z : S) :
    (atPrimeXToPowerSeries O K S z).order = IsDiscreteValuationRing.addVal S z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  obtain ⟨n, u, rfl⟩ := exists_associated_X_pow_atPrime (O := O) S hz
  rw [mul_comm, IsDiscreteValuationRing.addVal_def' u
    (prime_algebraMap_X_atPrime (O := O) S).irreducible, ← addVal_eq_order, map_mul, map_pow,
    atPrimeXToPowerSeries_algebraMap, map_X]
  exact IsDiscreteValuationRing.addVal_def' (Units.map (atPrimeXToPowerSeries O K S).toMonoidHom u)
    X_irreducible n
instance isLocalHom_atPrimeXToPowerSeries : IsLocalHom (atPrimeXToPowerSeries O K S) where
  map_nonunit z hz := by
    have := isDomain_atPrime_X (O := O) S
    have := isDiscreteValuationRing_atPrime_X (O := O) S
    rwa [← IsDiscreteValuationRing.addVal_eq_zero_iff, ← order_atPrimeXToPowerSeries (O := O) K,
      ← addVal_eq_order, IsDiscreteValuationRing.addVal_eq_zero_iff]
end FractionField
section Away
open AlgebraicGeometry
universe u
variable {R : Type*} [CommRing R] [IsDomain R] {f : R} (hf : f ≠ 0)
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away f S]
include hf
omit hf
end Away
end GlobalTheory.ChartRing


