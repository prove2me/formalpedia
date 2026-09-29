-- Prove2me | solution 1 for Algebra.FormallySmooth.exists_powerSeries_expansion_along_section_apply_eq_X
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/ab758db8-c13e-5c91-b635-9efca28a8432

import Mathlib
import Theorems.Thm_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section_apply_eq_X

set_option autoImplicit false

universe u v

namespace Algebra
p2m_export "Algebra" "FormallySmooth commutes mk algebraMap FormallySmooth.exists_powerSeries_expansion_along_section"
namespace FormallySmooth
p2m_export "Algebra.FormallySmooth" "comp mk exists_powerSeries_expansion_along_section"
namespace ExpansionEqXAux
p2m_open "Algebra.FormallySmooth Algebra"

open PowerSeries

variable {R : Type u} [CommRing R]

theorem X_dvd_of_X_pow_succ_dvd_X_pow_mul {n : ℕ} {r : PowerSeries R}
    (h : (X : PowerSeries R) ^ (n + 1) ∣ X ^ n * r) : (X : PowerSeries R) ∣ r := by
  rw [X_dvd_iff]
  rw [X_pow_dvd_iff] at h
  have := h n (Nat.lt_succ_self n)
  simpa [coeff_X_pow_mul', coeff_zero_eq_constantCoeff] using this

section subst

variable {f : PowerSeries R} (h0 : constantCoeff f = 0)

noncomputable def φ (h0 : constantCoeff f = 0) : PowerSeries R →ₐ[R] PowerSeries R :=
  PowerSeries.substAlgHom (HasSubst.of_constantCoeff_zero' h0)

theorem φ_X : φ h0 X = f := PowerSeries.substAlgHom_X _

theorem φ_C (r : R) : φ h0 (C r) = C r := by
  rw [C_eq_algebraMap, AlgHom.commutes]

include h0 in
theorem X_dvd_f : (X : PowerSeries R) ∣ f := X_dvd_iff.mpr h0

theorem X_pow_dvd_φ {n : ℕ} {p : PowerSeries R} (hp : (X : PowerSeries R) ^ n ∣ p) :
    (X : PowerSeries R) ^ n ∣ φ h0 p := by
  obtain ⟨q, rfl⟩ := hp
  rw [map_mul, map_pow, φ_X]
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (X_dvd_f h0) n) _

theorem constantCoeff_φ (p : PowerSeries R) : constantCoeff (φ h0 p) = constantCoeff p := by
  have hp : (X : PowerSeries R) ∣ p - C (constantCoeff p) := by
    rw [X_dvd_iff, map_sub, constantCoeff_C, sub_self]
  obtain ⟨q, hq⟩ := hp
  have : p = C (constantCoeff p) + X * q := by rw [← hq]; ring
  conv_lhs => rw [this, map_add, map_mul, φ_C, φ_X]
  rw [map_add, constantCoeff_C, map_mul, h0, zero_mul, add_zero]

variable (h1 : IsUnit (coeff 1 f))

include h1 in

theorem X_pow_dvd_of_X_pow_dvd_φ (n : ℕ) :
    ∀ p : PowerSeries R, (X : PowerSeries R) ^ n ∣ φ h0 p → (X : PowerSeries R) ^ n ∣ p := by
  obtain ⟨g, hg⟩ := X_dvd_f h0
  have hgc : IsUnit (constantCoeff g) := by
    have : coeff 1 f = constantCoeff g := by
      rw [hg, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff]
    rwa [this] at h1
  induction n with
  | zero => intro p _; simp
  | succ n ih =>
    intro p hp
    obtain ⟨q, rfl⟩ := ih p (dvd_trans (pow_dvd_pow X (Nat.le_succ n)) hp)
    rw [map_mul, map_pow, φ_X] at hp
    have hfn : f ^ n * φ h0 q = X ^ n * (g ^ n * φ h0 q) := by
      rw [← mul_assoc, ← mul_pow, ← hg]
    rw [hfn] at hp
    have hX := X_dvd_of_X_pow_succ_dvd_X_pow_mul hp
    rw [X_dvd_iff, map_mul, map_pow, constantCoeff_φ] at hX
    have hq : constantCoeff q = 0 :=
      ((hgc.pow n).mul_right_eq_zero).mp hX
    obtain ⟨q', rfl⟩ := X_dvd_iff.mpr hq
    rw [pow_succ]
    exact mul_dvd_mul_left _ (dvd_mul_right _ _)

include h1 in
theorem φ_injective : Function.Injective (φ h0) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  ext m
  have := X_pow_dvd_of_X_pow_dvd_φ h0 h1 (m + 1) p (by rw [hp]; exact dvd_zero _)
  rw [X_pow_dvd_iff] at this
  simpa using this m (Nat.lt_succ_self m)

noncomputable def approx (c' : R) (q : PowerSeries R) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 => approx c' q n + C (coeff n (q - φ h0 (approx c' q n)) * c' ^ n) * X ^ n

theorem approx_succ (c' : R) (q : PowerSeries R) (n : ℕ) :
    approx h0 c' q (n + 1) = approx h0 c' q n + C (coeff n (q - φ h0 (approx h0 c' q n)) * c' ^ n) * X ^ n :=
  rfl

theorem X_pow_dvd_approx_sub (c' : R) (q : PowerSeries R) (n : ℕ) :
    ∀ m : ℕ, n ≤ m → (X : PowerSeries R) ^ n ∣ approx h0 c' q m - approx h0 c' q n := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [approx_succ, add_sub_right_comm]
    exact dvd_add ih (dvd_mul_of_dvd_right (pow_dvd_pow X hm) _)

theorem X_pow_dvd_sub_φ_approx {c' : R} (hc' : coeff 1 f * c' = 1) (q : PowerSeries R) (n : ℕ) :
    (X : PowerSeries R) ^ n ∣ q - φ h0 (approx h0 c' q n) := by
  obtain ⟨g, hg⟩ := X_dvd_f h0
  have hgc : constantCoeff g = coeff 1 f := by
    rw [hg, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff]
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨w, hw⟩ := ih
    rw [approx_succ, map_add, ← sub_sub, hw, map_mul, φ_C, map_pow, φ_X]
    have hcoeff : coeff n (X ^ n * w) = constantCoeff w := by
      simp [coeff_X_pow_mul', coeff_zero_eq_constantCoeff]
    rw [hcoeff, hg, mul_pow, show (X : PowerSeries R) ^ n * w - C (constantCoeff w * c' ^ n) * (X ^ n * g ^ n) =
      X ^ n * (w - C (constantCoeff w * c' ^ n) * g ^ n) by ring]
    rw [pow_succ]
    refine mul_dvd_mul_left _ (X_dvd_iff.mpr ?_)
    rw [map_sub, map_mul, constantCoeff_C, map_pow, hgc, mul_assoc, ← mul_pow, mul_comm c', hc', one_pow,
      mul_one, sub_self]

include h1 in
theorem φ_surjective : Function.Surjective (φ h0) := by
  obtain ⟨c', hc'⟩ := h1.exists_right_inv
  intro q
  let s := approx h0 c' q
  refine ⟨PowerSeries.mk fun k => coeff k (s (k + 1)), ?_⟩
  set p : PowerSeries R := PowerSeries.mk fun k => coeff k (s (k + 1)) with hpdef

  have hp : ∀ n : ℕ, (X : PowerSeries R) ^ n ∣ p - s n := by
    intro n
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, hpdef, coeff_mk, sub_eq_zero]
    have h := X_pow_dvd_approx_sub h0 c' q (m + 1) n hm
    rw [X_pow_dvd_iff] at h
    have := h m (Nat.lt_succ_self m)
    rw [map_sub, sub_eq_zero] at this
    exact this.symm

  ext m
  have h1' : (X : PowerSeries R) ^ (m + 1) ∣ φ h0 p - q := by
    have a := X_pow_dvd_φ h0 (hp (m + 1))
    have b := X_pow_dvd_sub_φ_approx h0 hc' q (m + 1)
    rw [map_sub] at a
    have := dvd_sub a b
    rwa [show φ h0 p - φ h0 (s (m + 1)) - (q - φ h0 (approx h0 c' q (m + 1))) = φ h0 p - q by
      simp only [s]; ring] at this
  rw [X_pow_dvd_iff] at h1'
  have := h1' m (Nat.lt_succ_self m)
  rwa [map_sub, sub_eq_zero] at this

end subst

end Algebra.FormallySmooth.ExpansionEqXAux

open Algebra.FormallySmooth.ExpansionEqXAux PowerSeries in

theorem solution
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FormallySmooth R A]
    (e : A →ₐ[R] R) [Module.Free R (RingHom.ker e.toRingHom).Cotangent]
    (he : Module.finrank R (RingHom.ker e.toRingHom).Cotangent = 1)
    (t₀ : A) (ht₀ : e t₀ = 0)
    (hgen : RingHom.ker e.toRingHom ≤ Ideal.span {t₀} ⊔ RingHom.ker e.toRingHom ^ 2) :
    ∃ θ : A →+* PowerSeries R,
      (∀ r : R, θ (algebraMap R A r) = PowerSeries.C r) ∧
      (∀ (n : ℕ) (a : A), (∀ k : ℕ, k < n → PowerSeries.coeff k (θ a) = 0) ↔
        a ∈ RingHom.ker e.toRingHom ^ n) ∧
      (∀ (n : ℕ) (p : PowerSeries R), ∃ a : A, ∀ k : ℕ, k < n →
        PowerSeries.coeff k (θ a) = PowerSeries.coeff k p) ∧
      θ t₀ = PowerSeries.X := by
  obtain ⟨θ, hC, hker, hsurj⟩ :=
    Algebra.FormallySmooth.exists_powerSeries_expansion_along_section e he

  have ht₀I : t₀ ∈ RingHom.ker e.toRingHom ^ 1 := by simpa [RingHom.mem_ker] using ht₀
  have h0 : constantCoeff (θ t₀) = 0 := by
    have := ((hker 1 t₀).mpr ht₀I) 0 Nat.one_pos
    rwa [coeff_zero_eq_constantCoeff_apply] at this

  have h1 : IsUnit (coeff 1 (θ t₀)) := by
    obtain ⟨a₁, ha₁⟩ := hsurj 2 X
    have ha₁I : a₁ ∈ RingHom.ker e.toRingHom := by
      have := (hker 1 a₁).mp (fun k hk => by
        obtain rfl : k = 0 := Nat.lt_one_iff.mp hk
        rw [ha₁ 0 (by norm_num), coeff_zero_X])
      simpa using this
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp (hgen ha₁I)
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    have hy1 : coeff 1 (θ y) = 0 := ((hker 2 y).mpr hy) 1 (by norm_num)
    have key : coeff 1 (θ a₁) = coeff 0 (θ r) * coeff 1 (θ t₀) := by
      rw [← hxy, map_add, map_add, hy1, add_zero, map_mul, coeff_mul, Finset.Nat.antidiagonal_succ]
      simp [h0]
    rw [ha₁ 1 (by norm_num), coeff_one_X] at key
    exact isUnit_iff_dvd_one.mpr ⟨_, key.trans (mul_comm _ _)⟩

  let Φ : PowerSeries R ≃ₐ[R] PowerSeries R :=
    AlgEquiv.ofBijective (φ h0) ⟨φ_injective h0 h1, φ_surjective h0 h1⟩
  have hΦ : ∀ p, Φ p = φ h0 p := fun p => rfl

  have key : ∀ (n : ℕ) (p : PowerSeries R),
      (∀ k : ℕ, k < n → coeff k (Φ.symm p) = 0) ↔ (∀ k : ℕ, k < n → coeff k p = 0) := by
    intro n p
    rw [← X_pow_dvd_iff, ← X_pow_dvd_iff]
    constructor
    · intro h
      have := X_pow_dvd_φ h0 h
      rwa [← hΦ, AlgEquiv.apply_symm_apply] at this
    · intro h
      apply X_pow_dvd_of_X_pow_dvd_φ h0 h1 n
      rwa [← hΦ, AlgEquiv.apply_symm_apply]
  refine ⟨Φ.symm.toAlgHom.toRingHom.comp θ, ?_, ?_, ?_, ?_⟩
  · intro r
    change Φ.symm (θ (algebraMap R A r)) = _
    rw [hC, C_eq_algebraMap, AlgEquiv.commutes]
  · intro n a
    change (∀ k : ℕ, k < n → coeff k (Φ.symm (θ a)) = 0) ↔ _
    rw [key, hker]
  · intro n p
    obtain ⟨a, ha⟩ := hsurj n (Φ p)
    refine ⟨a, ?_⟩
    change ∀ k : ℕ, k < n → coeff k (Φ.symm (θ a)) = coeff k p
    have h' : ∀ k : ℕ, k < n → coeff k (Φ.symm (θ a - Φ p)) = 0 := by
      rw [key]
      intro k hk
      rw [map_sub, ha k hk, sub_self]
    intro k hk
    have := h' k hk
    rwa [map_sub, AlgEquiv.symm_apply_apply, map_sub, sub_eq_zero] at this
  · change Φ.symm (θ t₀) = X
    rw [AlgEquiv.symm_apply_eq, hΦ, φ_X]

end S_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section_apply_eq_X
end P2MW
export P2MW.S_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section_apply_eq_X (solution)
