-- Prove2me | solution 1 for Algebra.FormallySmooth.exists_powerSeries_expansion_along_section
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/9fdbed01-1025-551a-a0d2-5883265c8ab5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section

open PowerSeries

universe u v

namespace P2M
namespace TadicPS

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

variable (R) in

noncomputable abbrev JX : Ideal R⟦X⟧ := Ideal.span {X}

theorem JX_pow (n : ℕ) : JX R ^ n = Ideal.span {(X : R⟦X⟧) ^ n} :=
  Ideal.span_singleton_pow X n

theorem mem_JX_pow {n : ℕ} {p : R⟦X⟧} : p ∈ JX R ^ n ↔ ∀ k, k < n → coeff k p = 0 := by
  rw [JX_pow, Ideal.mem_span_singleton, X_pow_dvd_iff]

theorem mem_JX {p : R⟦X⟧} : p ∈ JX R ↔ constantCoeff p = 0 := by
  rw [Ideal.mem_span_singleton, X_dvd_iff]

theorem coeff_eq_of_mk_eq {n k : ℕ} (hk : k < n) {p q : R⟦X⟧}
    (h : Ideal.Quotient.mk (JX R ^ n) p = Ideal.Quotient.mk (JX R ^ n) q) :
    coeff k p = coeff k q := by
  rw [Ideal.Quotient.eq, mem_JX_pow] at h
  have := h k hk
  rwa [map_sub, sub_eq_zero] at this

theorem X_pow_succ_dvd_X_pow_mul_iff {n : ℕ} {y : R⟦X⟧} :
    (X : R⟦X⟧) ^ (n + 1) ∣ X ^ n * y ↔ constantCoeff y = 0 := by
  constructor
  · intro h
    have h' := (X_pow_dvd_iff.mp h) n (Nat.lt_succ_self n)
    rwa [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply] at h'
  · intro h
    obtain ⟨z, rfl⟩ := X_dvd_iff.mpr h
    exact ⟨z, by ring⟩

theorem JX_pow_le (n : ℕ) : JX R ^ (n + 2) ≤ JX R ^ (n + 1) :=
  Ideal.pow_le_pow_right (Nat.le_succ _)

theorem isNilpotent_ker_factor (n : ℕ) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor (JX_pow_le (R := R) n))) := by
  refine ⟨2, ?_⟩
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, ← pow_mul, Ideal.zero_eq_bot,
    Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact Ideal.pow_le_pow_right (by omega)

theorem strictMono_add_two : StrictMono fun k : ℕ => k + 2 :=
  fun _ _ h => Nat.add_lt_add_right h 2

variable (e : A →ₐ[R] R)

abbrev kerI : Ideal A := RingHom.ker e.toRingHom

theorem mem_kerI {a : A} : a ∈ kerI e ↔ e a = 0 := RingHom.mem_ker

theorem e_algebraMap (r : R) : e (algebraMap R A r) = r := e.commutes r

theorem sub_algebraMap_mem (a : A) : a - algebraMap R A (e a) ∈ kerI e := by
  rw [mem_kerI, map_sub, e_algebraMap, sub_self]

noncomputable def projI : A →ₗ[R] kerI e :=
  LinearMap.codRestrict ((kerI e).restrictScalars R)
    (LinearMap.id - (Algebra.linearMap R A) ∘ₗ e.toLinearMap) (sub_algebraMap_mem e)

@[scoped simp]
theorem projI_coe (a : A) : (projI e a : A) = a - algebraMap R A (e a) := rfl

def IsPointDerivation (D : A →ₗ[R] R) : Prop :=
  ∀ a b : A, D (a * b) = e a * D b + e b * D a

namespace IsPointDerivation

variable {e} {D : A →ₗ[R] R}

theorem map_one (hD : IsPointDerivation e D) : D 1 = 0 := by
  have h := hD 1 1
  rw [mul_one, _root_.map_one e, one_mul] at h
  linear_combination -h

theorem map_algebraMap (hD : IsPointDerivation e D) (r : R) : D (algebraMap R A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, hD.map_one, smul_zero]

end IsPointDerivation

section Lift

noncomputable def sigma2 {D : A →ₗ[R] R} (hD : IsPointDerivation e D) :
    A →ₐ[R] (R⟦X⟧ ⧸ JX R ^ 2) where
  toFun a := Ideal.Quotient.mk (JX R ^ 2) (C (e a) + C (D a) * X)
  map_one' := by
    simp only [_root_.map_one, hD.map_one, map_zero, zero_mul, add_zero]
  map_mul' a b := by
    show Ideal.Quotient.mk (JX R ^ 2) (C (e (a * b)) + C (D (a * b)) * X) =
      Ideal.Quotient.mk (JX R ^ 2) (C (e a) + C (D a) * X) *
        Ideal.Quotient.mk (JX R ^ 2) (C (e b) + C (D b) * X)
    rw [← _root_.map_mul (Ideal.Quotient.mk (JX R ^ 2)), Ideal.Quotient.eq]
    have h : C (e (a * b)) + C (D (a * b)) * X - (C (e a) + C (D a) * X) * (C (e b) + C (D b) * X)
        = -(C (D a * D b) * (X : R⟦X⟧) ^ 2) := by
      simp only [_root_.map_mul, hD a b, map_add]
      ring
    rw [h]
    exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self X) 2))
  map_zero' := by
    simp only [map_zero, zero_mul, add_zero]
  map_add' a b := by
    show Ideal.Quotient.mk (JX R ^ 2) (C (e (a + b)) + C (D (a + b)) * X) =
      Ideal.Quotient.mk (JX R ^ 2) (C (e a) + C (D a) * X) +
        Ideal.Quotient.mk (JX R ^ 2) (C (e b) + C (D b) * X)
    rw [← map_add (Ideal.Quotient.mk (JX R ^ 2))]
    congr 1
    simp only [map_add]
    ring
  commutes' r := by
    show Ideal.Quotient.mk (JX R ^ 2) (C (e (algebraMap R A r)) + C (D (algebraMap R A r)) * X) =
      algebraMap R (R⟦X⟧ ⧸ JX R ^ 2) r
    rw [e_algebraMap, hD.map_algebraMap, map_zero, zero_mul, add_zero]
    rfl

theorem sigma2_apply {D : A →ₗ[R] R} (hD : IsPointDerivation e D) (a : A) :
    sigma2 e hD a = Ideal.Quotient.mk (JX R ^ 2) (C (e a) + C (D a) * X) := rfl

variable [Algebra.FormallySmooth R A]

noncomputable def liftStep (n : ℕ) (σ : A →ₐ[R] (R⟦X⟧ ⧸ JX R ^ (n + 1))) :
    A →ₐ[R] (R⟦X⟧ ⧸ JX R ^ (n + 2)) :=
  Algebra.FormallySmooth.liftOfSurjective σ (Ideal.Quotient.factorₐ R (JX_pow_le n))
    (Ideal.Quotient.factor_surjective (JX_pow_le n)) (isNilpotent_ker_factor n)

theorem factor_comp_liftStep (n : ℕ) (σ : A →ₐ[R] (R⟦X⟧ ⧸ JX R ^ (n + 1))) :
    (Ideal.Quotient.factorₐ R (JX_pow_le n)).comp (liftStep n σ) = σ :=
  Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _

noncomputable def tower {D : A →ₗ[R] R} (hD : IsPointDerivation e D) :
    (k : ℕ) → (A →ₐ[R] (R⟦X⟧ ⧸ JX R ^ (k + 2)))
  | 0 => sigma2 e hD
  | k + 1 => liftStep (k + 1) (tower hD k)

theorem tower_zero {D : A →ₗ[R] R} (hD : IsPointDerivation e D) : tower e hD 0 = sigma2 e hD :=
  rfl

theorem tower_succ {D : A →ₗ[R] R} (hD : IsPointDerivation e D) (k : ℕ) :
    tower e hD (k + 1) = liftStep (k + 1) (tower e hD k) :=
  rfl

theorem tower_compat {D : A →ₗ[R] R} (hD : IsPointDerivation e D) (m : ℕ) :
    (Ideal.Quotient.factorPow (JX R) (strictMono_add_two.monotone m.le_succ)).comp
      (tower e hD (m + 1)).toRingHom = (tower e hD m).toRingHom :=
  congrArg AlgHom.toRingHom (factor_comp_liftStep (m + 1) (tower e hD m))

noncomputable def theta {D : A →ₗ[R] R} (hD : IsPointDerivation e D) : A →+* R⟦X⟧ :=
  IsAdicComplete.StrictMono.liftRingHom (JX R) strictMono_add_two
    (fun k => (tower e hD k).toRingHom) (fun {m} => tower_compat e hD m)

theorem mk_theta {D : A →ₗ[R] R} (hD : IsPointDerivation e D) (k : ℕ) (a : A) :
    Ideal.Quotient.mk (JX R ^ (k + 2)) (theta e hD a) = tower e hD k a :=
  IsAdicComplete.StrictMono.mk_liftRingHom (JX R) strictMono_add_two
    (fun k => (tower e hD k).toRingHom) (fun {m} => tower_compat e hD m) (n := k) a

theorem theta_algebraMap {D : A →ₗ[R] R} (hD : IsPointDerivation e D) (r : R) :
    theta e hD (algebraMap R A r) = C r := by
  ext k
  refine coeff_eq_of_mk_eq (n := k + 2) (by omega) ?_
  rw [mk_theta, AlgHom.commutes, ← Ideal.Quotient.mk_algebraMap, ← C_eq_algebraMap]

theorem mk_two_theta {D : A →ₗ[R] R} (hD : IsPointDerivation e D) (a : A) :
    Ideal.Quotient.mk (JX R ^ 2) (theta e hD a) =
      Ideal.Quotient.mk (JX R ^ 2) (C (e a) + C (D a) * X) :=
  mk_theta e hD 0 a

theorem constantCoeff_theta {D : A →ₗ[R] R} (hD : IsPointDerivation e D) (a : A) :
    constantCoeff (theta e hD a) = e a := by
  have h0 := coeff_eq_of_mk_eq (show 0 < 2 by norm_num) (mk_two_theta e hD a)
  rwa [map_add, coeff_zero_C, coeff_zero_mul_X, add_zero, coeff_zero_eq_constantCoeff_apply] at h0

theorem coeff_one_theta {D : A →ₗ[R] R} (hD : IsPointDerivation e D) (a : A) :
    coeff 1 (theta e hD a) = D a := by
  have h1 := coeff_eq_of_mk_eq (show 1 < 2 by norm_num) (mk_two_theta e hD a)
  rwa [map_add, coeff_C_mul, coeff_one_X, coeff_C, if_neg one_ne_zero, zero_add, mul_one] at h1

end Lift

section Triangular

variable {e}

theorem theta_mem_JX {θ : A →+* R⟦X⟧} (hθ0 : ∀ a, constantCoeff (θ a) = e a) {a : A}
    (ha : a ∈ kerI e) : θ a ∈ JX R := by
  rw [mem_JX, hθ0]
  exact (mem_kerI e).mp ha

theorem theta_mem_JX_pow {θ : A →+* R⟦X⟧} (hθ0 : ∀ a, constantCoeff (θ a) = e a) {n : ℕ}
    {a : A} (ha : a ∈ kerI e ^ n) : θ a ∈ JX R ^ n := by
  have h1 : kerI e ≤ (JX R).comap θ := fun x hx => theta_mem_JX hθ0 hx
  exact ((Ideal.pow_right_mono h1 n).trans (Ideal.le_comap_pow θ n)) ha

theorem gen_pow {t₀ : A} (ht₀ : t₀ ∈ kerI e)
    (hgen : ∀ x ∈ kerI e, ∃ r : R, x - algebraMap R A r * t₀ ∈ kerI e ^ 2) (n : ℕ) :
    ∀ b ∈ kerI e ^ n, ∃ r : R, b - algebraMap R A r * t₀ ^ n ∈ kerI e ^ (n + 1) := by
  induction n with
  | zero =>
    intro b _
    refine ⟨e b, ?_⟩
    rw [pow_zero, mul_one, zero_add, pow_one]
    exact sub_algebraMap_mem e b
  | succ n ih =>
    intro b hb
    rw [pow_succ] at hb
    refine Submodule.mul_induction_on hb ?_ ?_
    · intro x hx y hy
      obtain ⟨r, hr⟩ := ih x hx
      obtain ⟨s, hs⟩ := hgen y hy
      refine ⟨r * s, ?_⟩
      have hxy : x * y - algebraMap R A (r * s) * t₀ ^ (n + 1) =
          (x - algebraMap R A r * t₀ ^ n) * y +
            algebraMap R A r * (t₀ ^ n * (y - algebraMap R A s * t₀)) := by
        rw [_root_.map_mul]
        ring
      rw [hxy]
      refine add_mem ?_ (Ideal.mul_mem_left _ _ ?_)
      · rw [pow_succ (kerI e) (n + 1)]
        exact Ideal.mul_mem_mul hr hy
      · show _ ∈ kerI e ^ (n + 2)
        rw [pow_add]
        exact Ideal.mul_mem_mul (Ideal.pow_mem_pow ht₀ n) hs
    · rintro x y ⟨r, hr⟩ ⟨s, hs⟩
      refine ⟨r + s, ?_⟩
      have hxy : x + y - algebraMap R A (r + s) * t₀ ^ (n + 1) =
          (x - algebraMap R A r * t₀ ^ (n + 1)) + (y - algebraMap R A s * t₀ ^ (n + 1)) := by
        rw [map_add]
        ring
      rw [hxy]
      exact add_mem hr hs

theorem exists_theta_t0_eq {θ : A →+* R⟦X⟧} (hθ0 : ∀ a, constantCoeff (θ a) = e a) {t₀ : A}
    (ht₀ : t₀ ∈ kerI e) (hθ1 : coeff 1 (θ t₀) = 1) :
    ∃ v : R⟦X⟧, θ t₀ = X * v ∧ constantCoeff v = 1 := by
  obtain ⟨v, hv⟩ : (X : R⟦X⟧) ∣ θ t₀ := X_dvd_iff.mpr (by rw [hθ0]; exact (mem_kerI e).mp ht₀)
  refine ⟨v, hv, ?_⟩
  have h := coeff_succ_X_mul 0 v
  rw [zero_add, ← hv, hθ1, coeff_zero_eq_constantCoeff_apply] at h
  exact h.symm

theorem mem_pow_of_theta_mem {θ : A →+* R⟦X⟧} (hθC : ∀ r, θ (algebraMap R A r) = C r)
    (hθ0 : ∀ a, constantCoeff (θ a) = e a) {t₀ : A} (ht₀ : t₀ ∈ kerI e)
    (hθ1 : coeff 1 (θ t₀) = 1)
    (hgen : ∀ x ∈ kerI e, ∃ r : R, x - algebraMap R A r * t₀ ∈ kerI e ^ 2) :
    ∀ (n : ℕ) (a : A), θ a ∈ JX R ^ n → a ∈ kerI e ^ n := by
  obtain ⟨v, hv, hv1⟩ := exists_theta_t0_eq hθ0 ht₀ hθ1
  intro n
  induction n with
  | zero =>
    intro a _
    simp
  | succ n ih =>
    intro a ha
    have ha' : θ a ∈ JX R ^ n := Ideal.pow_le_pow_right n.le_succ ha
    obtain ⟨r, hr⟩ := gen_pow ht₀ hgen n a (ih a ha')
    have h1 : θ (a - algebraMap R A r * t₀ ^ n) ∈ JX R ^ (n + 1) := theta_mem_JX_pow hθ0 hr
    have h2 : θ (algebraMap R A r * t₀ ^ n) ∈ JX R ^ (n + 1) := by
      have := sub_mem ha h1
      rwa [map_sub, sub_sub_cancel] at this
    rw [_root_.map_mul, map_pow, hθC, hv, JX_pow, Ideal.mem_span_singleton,
      show C r * (X * v) ^ n = X ^ n * (C r * v ^ n) by ring,
      X_pow_succ_dvd_X_pow_mul_iff, _root_.map_mul, map_pow, hv1, one_pow, mul_one,
      constantCoeff_C] at h2
    rw [h2, map_zero, zero_mul, sub_zero] at hr
    exact hr

theorem exists_sub_theta_mem {θ : A →+* R⟦X⟧} (hθC : ∀ r, θ (algebraMap R A r) = C r)
    (hθ0 : ∀ a, constantCoeff (θ a) = e a) {t₀ : A} (ht₀ : t₀ ∈ kerI e)
    (hθ1 : coeff 1 (θ t₀) = 1) :
    ∀ (n : ℕ) (p : R⟦X⟧), ∃ a : A, p - θ a ∈ JX R ^ n := by
  obtain ⟨v, hv, hv1⟩ := exists_theta_t0_eq hθ0 ht₀ hθ1
  intro n
  induction n with
  | zero =>
    intro p
    exact ⟨0, by simp⟩
  | succ n ih =>
    intro p
    obtain ⟨a, ha⟩ := ih p
    rw [JX_pow, Ideal.mem_span_singleton] at ha
    obtain ⟨w, hw⟩ := ha
    refine ⟨a + algebraMap R A (constantCoeff w) * t₀ ^ n, ?_⟩
    rw [JX_pow, Ideal.mem_span_singleton, map_add, _root_.map_mul, map_pow, hθC, hv,
      show p - (θ a + C (constantCoeff w) * (X * v) ^ n) =
        (p - θ a) - C (constantCoeff w) * (X * v) ^ n by ring,
      hw,
      show X ^ n * w - C (constantCoeff w) * (X * v) ^ n =
        X ^ n * (w - C (constantCoeff w) * v ^ n) by ring,
      X_pow_succ_dvd_X_pow_mul_iff, map_sub, _root_.map_mul, map_pow, hv1, one_pow, mul_one,
      constantCoeff_C, sub_self]

end Triangular

theorem main [Algebra.FormallySmooth R A] {D : A →ₗ[R] R} (hD : IsPointDerivation e D)
    {t₀ : A} (ht₀ : t₀ ∈ kerI e) (hDt : D t₀ = 1)
    (hgen : ∀ x ∈ kerI e, ∃ r : R, x - algebraMap R A r * t₀ ∈ kerI e ^ 2) :
    ∃ θ : A →+* PowerSeries R,
      (∀ r : R, θ (algebraMap R A r) = PowerSeries.C r) ∧
      (∀ (n : ℕ) (a : A), (∀ k : ℕ, k < n → PowerSeries.coeff k (θ a) = 0) ↔
        a ∈ kerI e ^ n) ∧
      (∀ (n : ℕ) (p : PowerSeries R), ∃ a : A, ∀ k : ℕ, k < n →
        PowerSeries.coeff k (θ a) = PowerSeries.coeff k p) := by
  have hθ1 : coeff 1 (theta e hD t₀) = 1 := by rw [coeff_one_theta, hDt]
  refine ⟨theta e hD, theta_algebraMap e hD, ?_, ?_⟩
  · intro n a
    rw [← mem_JX_pow]
    exact ⟨mem_pow_of_theta_mem (theta_algebraMap e hD) (constantCoeff_theta e hD) ht₀ hθ1 hgen
      n a, theta_mem_JX_pow (constantCoeff_theta e hD)⟩
  · intro n p
    obtain ⟨a, ha⟩ :=
      exists_sub_theta_mem (theta_algebraMap e hD) (constantCoeff_theta e hD) ht₀ hθ1 n p
    refine ⟨a, fun k hk => ?_⟩
    have := (mem_JX_pow.mp ha) k hk
    rw [map_sub, sub_eq_zero] at this
    exact this.symm

theorem exists_data [Module.Free R (kerI e).Cotangent]
    (he : Module.finrank R (kerI e).Cotangent = 1) :
    ∃ (D : A →ₗ[R] R) (t₀ : A), IsPointDerivation e D ∧ t₀ ∈ kerI e ∧ D t₀ = 1 ∧
      ∀ x ∈ kerI e, ∃ r : R, x - algebraMap R A r * t₀ ∈ kerI e ^ 2 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI := Module.subsingleton R A
    refine ⟨0, 0, fun a b => by simp, Ideal.zero_mem _, Subsingleton.elim _ _, fun x _ => ⟨0, ?_⟩⟩
    rw [Subsingleton.elim (x - algebraMap R A 0 * 0) 0]
    exact Ideal.zero_mem _
  · let b := Module.basisUnique Unit he
    obtain ⟨t, ht⟩ := (kerI e).toCotangent_surjective (b default)
    refine ⟨(b.coord default) ∘ₗ ((kerI e).toCotangent.restrictScalars R) ∘ₗ projI e, t, ?_,
      t.2, ?_, ?_⟩
    · intro a c
      have key : (kerI e).toCotangent (projI e (a * c)) =
          e a • (kerI e).toCotangent (projI e c) + e c • (kerI e).toCotangent (projI e a) := by
        rw [← LinearMap.map_smul_of_tower ((kerI e).toCotangent) (e a),
          ← LinearMap.map_smul_of_tower ((kerI e).toCotangent) (e c), ← map_add]
        refine ((kerI e).toCotangent_eq).mpr ?_
        have hcoe : (projI e (a * c) : A) - ((e a • projI e c + e c • projI e a : kerI e) : A) =
            (a - algebraMap R A (e a)) * (c - algebraMap R A (e c)) := by
          simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, projI_coe,
            Algebra.smul_def, _root_.map_mul]
          ring
        rw [hcoe, pow_two]
        exact Ideal.mul_mem_mul (sub_algebraMap_mem e a) (sub_algebraMap_mem e c)
      show b.coord default ((kerI e).toCotangent (projI e (a * c))) =
        e a * b.coord default ((kerI e).toCotangent (projI e c)) +
          e c * b.coord default ((kerI e).toCotangent (projI e a))
      rw [key, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    · have hproj : projI e (t : A) = t :=
        Subtype.ext (by rw [projI_coe, (mem_kerI e).mp t.2, map_zero, sub_zero])
      show b.coord default ((kerI e).toCotangent (projI e (t : A))) = 1
      rw [hproj, ht, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
    · intro x hx
      have h1 : b.repr ((kerI e).toCotangent ⟨x, hx⟩) default • b default =
          (kerI e).toCotangent ⟨x, hx⟩ := by
        simpa using b.sum_repr ((kerI e).toCotangent ⟨x, hx⟩)
      refine ⟨b.repr ((kerI e).toCotangent ⟨x, hx⟩) default, ?_⟩
      rw [← ht, ← LinearMap.map_smul_of_tower] at h1
      have h2 := ((kerI e).toCotangent_eq).mp h1.symm
      rw [Submodule.coe_smul_of_tower, Algebra.smul_def] at h2
      exact h2

end P2M.TadicPS
p2m_reactivate "P2MW.S_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section.P2M P2MW.S_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section.P2M.TadicPS"
p2m_reactivate "P2MW.S_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section.P2M"

theorem solution
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FormallySmooth R A]
    (e : A →ₐ[R] R) [Module.Free R (RingHom.ker e.toRingHom).Cotangent]
    (he : Module.finrank R (RingHom.ker e.toRingHom).Cotangent = 1) :
    ∃ θ : A →+* PowerSeries R,
      (∀ r : R, θ (algebraMap R A r) = PowerSeries.C r) ∧
      (∀ (n : ℕ) (a : A), (∀ k : ℕ, k < n → PowerSeries.coeff k (θ a) = 0) ↔
        a ∈ RingHom.ker e.toRingHom ^ n) ∧
      (∀ (n : ℕ) (p : PowerSeries R), ∃ a : A, ∀ k : ℕ, k < n →
        PowerSeries.coeff k (θ a) = PowerSeries.coeff k p) := by
  obtain ⟨D, t₀, hD, ht₀, hDt, hgen⟩ := P2M.TadicPS.exists_data e he
  exact P2M.TadicPS.main e hD ht₀ hDt hgen

end S_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section
end P2MW
export P2MW.S_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section (solution)
