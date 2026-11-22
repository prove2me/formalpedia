-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatRing
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_GatRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:09:54.063583+00:00
-- url     : https://prove2.me/theorems/56a0b192-dda9-4e30-8905-d7726013cf55
-- title:
--   Gat Ring
-- statement:
--   Definitions and structural lemmas for Gat Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GatRing.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂.GatR
open QuadraticAlgebra IsLocalRing
variable {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] {ϖ : W}
theorem om_sq : (ω : QuadraticAlgebra W ϖ 0) ^ 2 = algebraMap W _ ϖ := by
  rw [sq, algebraMap_eq]; ext <;> simp
theorem om_pow (n : ℕ) : (ω : QuadraticAlgebra W ϖ 0) ^ (2 * n) = algebraMap W _ (ϖ ^ n) := by
  rw [pow_mul, om_sq, map_pow]
theorem isUnit_of_re (hϖ : Irreducible ϖ) (z : QuadraticAlgebra W ϖ 0) (h : IsUnit z.re) : IsUnit z := by
  rw [isUnit_iff_norm_isUnit, norm_def]
  by_contra hn
  have h1 : ϖ * z.im * z.im ∈ nonunits W := fun hu =>
    hϖ.not_isUnit (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hu))
  have h2 := nonunits_add (show _ ∈ nonunits W from hn) h1
  have e : z.re * z.re + 0 * z.re * z.im - ϖ * z.im * z.im + ϖ * z.im * z.im = z.re * z.re := by ring
  rw [e] at h2
  exact h2 (h.mul h)
theorem om_not_isUnit (hϖ : Irreducible ϖ) : ¬ IsUnit (ω : QuadraticAlgebra W ϖ 0) := by
  rw [isUnit_iff_norm_isUnit, norm_def]
  simp only [omega_re, omega_im]
  intro h
  have e : (0 : W) * 0 + 0 * 0 * 1 - ϖ * 1 * 1 = -ϖ := by ring
  rw [e, IsUnit.neg_iff] at h
  exact hϖ.not_isUnit h
theorem fact (hϖ : Irreducible ϖ) (z : QuadraticAlgebra W ϖ 0) (hz : z ≠ 0) :
    ∃ (n : ℕ) (u : QuadraticAlgebra W ϖ 0), IsUnit u ∧ z = ω ^ n * u := by
  have caseB : ∀ (j : ℕ) (v : Wˣ) (a' : W), z.im = v * ϖ ^ j → z.re = ϖ ^ (j + 1) * a' →
      ∃ (n : ℕ) (u : QuadraticAlgebra W ϖ 0), IsUnit u ∧ z = ω ^ n * u := fun j v a' h1 h2 => by
    refine ⟨2 * j + 1, ⟨v, a'⟩, isUnit_of_re hϖ _ v.isUnit, ?_⟩
    rw [pow_succ, om_pow, algebraMap_eq]
    ext
    · simp only [re_mul, im_mul, omega_re, omega_im, h2]; ring
    · simp only [re_mul, im_mul, omega_re, omega_im, h1]; ring
  by_cases ha : z.re = 0
  · have hb : z.im ≠ 0 := fun hb => hz (by ext <;> simp [ha, hb])
    obtain ⟨j, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
    exact caseB j v 0 hv (by rw [ha, mul_zero])
  · obtain ⟨i, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    by_cases hd : ϖ ^ i ∣ z.im
    · obtain ⟨b', hb'⟩ := hd
      refine ⟨2 * i, ⟨u, b'⟩, isUnit_of_re hϖ _ u.isUnit, ?_⟩
      rw [om_pow, algebraMap_eq]
      ext
      · simp [hu]; ring
      · simp [hb']
    · have hb : z.im ≠ 0 := fun hb => hd (by rw [hb]; exact dvd_zero _)
      obtain ⟨j, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
      have hji : j < i := by
        by_contra hc
        exact hd (hv ▸ Dvd.dvd.mul_left (pow_dvd_pow ϖ (not_lt.mp hc)) _)
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hji
      exact caseB j v (u * ϖ ^ c) hv (by rw [hu]; ring)
theorem om_pow_ne_zero (hϖ : Irreducible ϖ) (n : ℕ) : (ω : QuadraticAlgebra W ϖ 0) ^ n ≠ 0 := by
  intro h
  have h2 : (ω : QuadraticAlgebra W ϖ 0) ^ (2 * n) = 0 := by rw [two_mul, pow_add, h, mul_zero]
  rw [om_pow, map_eq_zero_iff _ algebraMap_injective] at h2
  exact pow_ne_zero n hϖ.ne_zero h2
theorem isDomain (hϖ : Irreducible ϖ) : IsDomain (QuadraticAlgebra W ϖ 0) := by
  have : NoZeroDivisors (QuadraticAlgebra W ϖ 0) := ⟨fun {x y} hxy => by
    by_contra hc
    rw [not_or] at hc
    obtain ⟨n, u, hu, rfl⟩ := fact hϖ x hc.1
    obtain ⟨m, v, hv, rfl⟩ := fact hϖ y hc.2
    have e : ω ^ n * u * (ω ^ m * v) = ω ^ (n + m) * (u * v) := by ring
    rw [e] at hxy
    exact om_pow_ne_zero hϖ (n + m) ((hu.mul hv).mul_left_eq_zero.mp hxy)⟩
  exact NoZeroDivisors.to_isDomain _
theorem om_irreducible (hϖ : Irreducible ϖ) : Irreducible (ω : QuadraticAlgebra W ϖ 0) := by
  have := isDomain hϖ
  refine ⟨om_not_isUnit hϖ, fun x y hxy => ?_⟩
  have h0 : (ω : QuadraticAlgebra W ϖ 0) ≠ 0 := by simpa using om_pow_ne_zero hϖ 1
  have hx : x ≠ 0 := fun h => h0 (by rw [hxy, h, zero_mul])
  have hy : y ≠ 0 := fun h => h0 (by rw [hxy, h, mul_zero])
  obtain ⟨n, u, hu, rfl⟩ := fact hϖ x hx
  obtain ⟨m, v, hv, rfl⟩ := fact hϖ y hy
  rcases n with _ | n
  · left; simpa using hu
  rcases m with _ | m
  · right; simpa using hv
  exfalso
  have e : (ω : QuadraticAlgebra W ϖ 0) * 1 = ω * (ω * (ω ^ (n + m) * (u * v))) := by
    rw [mul_one]; conv_lhs => rw [hxy]
    ring
  exact om_not_isUnit hϖ (IsUnit.of_mul_eq_one _ (mul_left_cancel₀ h0 e).symm)
theorem isDVR (hϖ : Irreducible ϖ) :
    haveI := isDomain hϖ; IsDiscreteValuationRing (QuadraticAlgebra W ϖ 0) := by
  have := isDomain hϖ
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨ω, om_irreducible hϖ, fun {x} hx => ?_⟩
  obtain ⟨n, u, hu, rfl⟩ := fact hϖ x hx
  exact ⟨n, hu.unit, rfl⟩
end Formalism.BasicNotions.Examples₂.GatR


