-- Prove2me | solution 1 for AlgebraicCurve.Place.eq_of_forall_coe_mem_nonunits_iff_of_isDedekindDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/732e7a49-23a6-5f9c-a598-46b7ea8928a7

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_eq_of_forall_coe_mem_nonunits_iff_of_isDedekindDomain

set_option autoImplicit false

namespace Ws47
namespace U1

open IsLocalRing

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (A : Subalgebra K F)
  [IsDedekindDomain ↥A] [IsFractionRing ↥A F]

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1600000 in

theorem mem_iff_exists (v : AlgebraicCurve.Place K F) (hv : ∀ a : ↥A, (a : F) ∈ v.toValuationSubring) (x : F) :
    x ∈ v.toValuationSubring ↔
      ∃ a s : ↥A, (s : F) ∉ v.toValuationSubring.nonunits ∧ x * (s : F) = (a : F) := by
  classical
  set O := v.toValuationSubring with hO
  have hcoe : ∀ a : ↥A, algebraMap (↥A) F a = (a : F) := fun _ => rfl

  have hval1 : ∀ s : ↥A, (s : F) ∉ O.nonunits → O.valuation (s : F) = 1 := fun s hs =>
    le_antisymm ((O.valuation_le_one_iff _).mpr (hv s)) (not_lt.mp fun h => hs (O.mem_nonunits_iff.mpr h))
  constructor
  swap
  · rintro ⟨a, s, hs, hxs⟩
    have hs1 := hval1 s hs
    have hs0 : (s : F) ≠ 0 := fun h => by rw [h, map_zero] at hs1; exact zero_ne_one hs1
    rw [← O.valuation_le_one_iff]
    have hx : x = (a : F) * (s : F)⁻¹ := by rw [← hxs, mul_inv_cancel_right₀ hs0]
    rw [hx, map_mul, map_inv₀, hs1, inv_one, mul_one]
    exact (O.valuation_le_one_iff _).mpr (hv a)
  intro hx

  let φ : ↥A →+* ↥O := (algebraMap (↥A) F).codRestrict O.toSubring hv
  have hφ : ∀ a : ↥A, ((φ a : ↥O) : F) = (a : F) := fun _ => rfl
  let P : Ideal ↥A := (maximalIdeal ↥O).comap φ
  have hP : ∀ a : ↥A, a ∈ P ↔ (a : F) ∈ O.nonunits := by
    intro a
    rw [Ideal.mem_comap, O.valuation_lt_one_iff, O.mem_nonunits_iff, hφ]
  haveI hPprime : P.IsPrime := Ideal.comap_isPrime φ (maximalIdeal ↥O)

  have hP0 : P ≠ ⊥ := by
    intro hbot
    apply v.ne_top'
    refine top_le_iff.mp fun y _ => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ↥A) y
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbP : b ∉ P := by rw [hbot, Ideal.mem_bot]; exact hb0
    have hb1 : O.valuation (b : F) = 1 := hval1 b ((hP b).not.mp hbP)
    show _ ∈ O
    rw [← O.valuation_le_one_iff, map_div₀, hcoe, hcoe, hb1, div_one]
    exact (O.valuation_le_one_iff _).mpr (hv a)

  let Aₚ := Localization.AtPrime P
  haveI : IsDiscreteValuationRing Aₚ :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (↥A) hP0 Aₚ
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap (↥A) F y) := by
    intro y
    refine isUnit_iff_ne_zero.mpr ?_
    rw [hcoe, Ne, ZeroMemClass.coe_eq_zero]
    exact fun h => y.2 (h ▸ P.zero_mem)
  letI : Algebra Aₚ F := (IsLocalization.lift (M := P.primeCompl) (S := Aₚ) hunit).toAlgebra
  have halg : ∀ z : Aₚ, algebraMap Aₚ F z = IsLocalization.lift (M := P.primeCompl) (S := Aₚ) hunit z := fun _ => rfl
  haveI : IsScalarTower (↥A) Aₚ F := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [halg, IsLocalization.lift_eq (M := P.primeCompl) (S := Aₚ) hunit a]
  haveI : IsFractionRing Aₚ F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl Aₚ F

  have hint : ∀ y : F, IsLocalization.IsInteger Aₚ y → ∃ a s : ↥A, s ∉ P ∧ y * (s : F) = (a : F) := by
    rintro y ⟨z, rfl⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl z
    refine ⟨a, s, s.2, ?_⟩
    have h := (IsLocalization.lift_mk'_spec (M := P.primeCompl) (S := Aₚ) hunit a
      (IsLocalization.lift (M := P.primeCompl) (S := Aₚ) hunit (IsLocalization.mk' Aₚ a s)) s).mp rfl

    rw [halg, mul_comm, ← hcoe a, h]
    rfl

  rcases (ValuationRing.iff_isInteger_or_isInteger Aₚ F).mp inferInstance x with h1 | h2
  · obtain ⟨a, s, hs, hxs⟩ := hint x h1
    exact ⟨a, s, (hP s).not.mp hs, hxs⟩
  · obtain ⟨a, s, hs, hxs⟩ := hint x⁻¹ h2
    by_cases ha : a ∈ P
    ·
      rcases eq_or_ne x 0 with rfl | hx0
      · exact ⟨0, 1, fun h1 => by
          rw [O.mem_nonunits_iff, OneMemClass.coe_one, map_one] at h1; exact lt_irrefl 1 h1,
          by rw [zero_mul, ZeroMemClass.coe_zero]⟩
      exfalso
      have hs1 := hval1 s ((hP s).not.mp hs)
      have ha1 : O.valuation (a : F) < 1 := O.mem_nonunits_iff.mp ((hP a).mp ha)
      have hxinv : O.valuation x⁻¹ < 1 := by
        have := congrArg O.valuation hxs
        rw [map_mul, hs1, mul_one] at this
        rwa [this]
      have hx1 : O.valuation x ≤ 1 := (O.valuation_le_one_iff _).mpr hx
      have : O.valuation x * O.valuation x⁻¹ < 1 :=
        calc O.valuation x * O.valuation x⁻¹ ≤ 1 * O.valuation x⁻¹ := mul_le_mul_left hx1 _
          _ < 1 := by rwa [one_mul]
      rw [← map_mul, mul_inv_cancel₀ hx0, map_one] at this
      exact lt_irrefl 1 this
    ·
      refine ⟨s, a, (hP a).not.mp ha, ?_⟩
      have ha0 : (a : F) ≠ 0 := by
        rw [Ne, ZeroMemClass.coe_eq_zero]; exact fun h => ha (h ▸ P.zero_mem)
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [inv_zero, zero_mul] at hxs
        exact ha0 hxs.symm
      have := congrArg (fun t => t * x) hxs
      rw [mul_assoc, mul_comm (s : F) x, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul] at this
      rw [mul_comm, this]

end Ws47.U1

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] (A : Subalgebra K F)
    [IsDedekindDomain ↥A] [IsFractionRing ↥A F]
    (v v' : AlgebraicCurve.Place K F)
    (hv : ∀ a : ↥A, (a : F) ∈ v.toValuationSubring) (hv' : ∀ a : ↥A, (a : F) ∈ v'.toValuationSubring)
    (h : ∀ a : ↥A, (a : F) ∈ v.toValuationSubring.nonunits ↔ (a : F) ∈ v'.toValuationSubring.nonunits) :
    v = v' := by
  refine AlgebraicCurve.Place.ext (SetLike.ext fun x => ?_)
  rw [Ws47.U1.mem_iff_exists A v hv x, Ws47.U1.mem_iff_exists A v' hv' x]
  simp only [h]

end S_AlgebraicCurve_Place_eq_of_forall_coe_mem_nonunits_iff_of_isDedekindDomain
end P2MW
export P2MW.S_AlgebraicCurve_Place_eq_of_forall_coe_mem_nonunits_iff_of_isDedekindDomain (solution)
