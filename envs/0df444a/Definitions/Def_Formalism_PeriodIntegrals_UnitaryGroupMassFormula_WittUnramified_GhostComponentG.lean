-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittUnramified_GhostComponentG
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittUnramified_GhostComponentG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:02:11.569807+00:00
-- url     : https://prove2.me/theorems/2e8e1b4d-fa00-43c3-a47e-f28b982f298f
-- title:
--   Ghost Component G
-- statement:
--   Definitions and structural lemmas for Ghost Component G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittUnramified/GhostComponentG.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WittUnram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WittUnramWork
open WittVector Finset
variable {p : ℕ} [hp : Fact p.Prime] {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]
section Restrict
def sigF (σ : Qq ≃+* Qq) (hσ : ∀ x : W, ∃ y : W, σ (algebraMap W Qq x) = algebraMap W Qq (x ^ p + (p : W) * y))
    (x : W) : W :=
  x ^ p + (p : W) * (hσ x).choose
theorem sigF_spec (σ : Qq ≃+* Qq)
    (hσ : ∀ x : W, ∃ y : W, σ (algebraMap W Qq x) = algebraMap W Qq (x ^ p + (p : W) * y)) (x : W) :
    algebraMap W Qq (sigF σ hσ x) = σ (algebraMap W Qq x) := (hσ x).choose_spec.symm
def sigW (hinj : Function.Injective (algebraMap W Qq)) (σ : Qq ≃+* Qq)
    (hσ : ∀ x : W, ∃ y : W, σ (algebraMap W Qq x) = algebraMap W Qq (x ^ p + (p : W) * y)) : W →+* W where
  toFun := sigF σ hσ
  map_one' := hinj (by rw [sigF_spec]; simp)
  map_mul' x y := hinj (by simp only [sigF_spec, map_mul])
  map_zero' := hinj (by rw [sigF_spec]; simp)
  map_add' x y := hinj (by simp only [sigF_spec, map_add])
end Restrict
section Dwork
variable (p Qq) [Invertible (p : Qq)] (F : W →+* W)
def G (x : W) : WittVector p Qq :=
  (ghostEquiv p Qq).symm (fun n => algebraMap W Qq ((F^[n]) x))
theorem ghostComponent_G (x : W) (n : ℕ) :
    ghostComponent n (G p Qq F x) = algebraMap W Qq ((F^[n]) x) := by
  have h := congrFun ((ghostEquiv p Qq).apply_symm_apply (fun n => algebraMap W Qq ((F^[n]) x))) n
  rw [← WittVector.ghostMap_apply, ← WittVector.ghostEquiv_coe p Qq]
  exact h
theorem ghost_sum_G (x : W) (k : ℕ) :
    ∑ i ∈ range (k + 1), (p : Qq) ^ i * (G p Qq F x).coeff i ^ p ^ (k - i) = algebraMap W Qq ((F^[k]) x) := by
  rw [← ghostComponent_G p Qq F x k, WittVector.ghostComponent_apply, wittPolynomial_eq_sum_C_mul_X_pow]
  simp [map_sum, MvPolynomial.aeval_X]
theorem G_coeff_zero (x : W) : (G p Qq F x).coeff 0 = algebraMap W Qq x := by
  have h := ghost_sum_G p Qq F x 0
  simpa using h
theorem G_add (x y : W) : G p Qq F (x + y) = G p Qq F x + G p Qq F y := by
  have hit : ∀ n, (F^[n]) = ⇑(F ^ n) := fun n => (RingHom.coe_pow F n).symm
  simp only [G]
  rw [← map_add]
  congr 1
  funext n
  simp only [Pi.add_apply, hit, map_add]
theorem G_mul (x y : W) : G p Qq F (x * y) = G p Qq F x * G p Qq F y := by
  have hit : ∀ n, (F^[n]) = ⇑(F ^ n) := fun n => (RingHom.coe_pow F n).symm
  simp only [G]
  rw [← map_mul]
  congr 1
  funext n
  simp only [Pi.mul_apply, hit, map_mul]
theorem G_one : G p Qq F (1 : W) = 1 := by
  have hit : ∀ n, (F^[n]) = ⇑(F ^ n) := fun n => (RingHom.coe_pow F n).symm
  simp only [G]
  rw [← map_one (ghostEquiv p Qq).symm]
  congr 1
  funext n
  simp only [Pi.one_apply, hit, map_one]
theorem G_zero : G p Qq F (0 : W) = 0 := by
  have hit : ∀ n, (F^[n]) = ⇑(F ^ n) := fun n => (RingHom.coe_pow F n).symm
  simp only [G]
  rw [← map_zero (ghostEquiv p Qq).symm]
  congr 1
  funext n
  simp only [Pi.zero_apply, hit, map_zero]
variable (hF : ∀ x : W, ∃ y : W, F x = x ^ p + (p : W) * y)
include hF
theorem G_coeff_integral (hinj : Function.Injective (algebraMap W Qq)) (x : W) (n : ℕ) :
    ∃ a : W, (G p Qq F x).coeff n = algebraMap W Qq a := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | k
  · exact ⟨x, G_coeff_zero p Qq F x⟩
  choose! b hb using ih
  have hbk : ∀ i ∈ range (k + 1), (G p Qq F x).coeff i = algebraMap W Qq (b i) :=
    fun i hi => hb i (by simp at hi; omega)
  have hk : (F^[k]) x = ∑ i ∈ range (k + 1), (p : W) ^ i * b i ^ p ^ (k - i) := by
    apply hinj
    rw [← ghost_sum_G p Qq F x k]
    simp only [map_sum, map_mul, map_pow, map_natCast]
    exact Finset.sum_congr rfl fun i hi => by rw [hbk i hi]
  have hk1 : (F^[k + 1]) x = ∑ i ∈ range (k + 1), (p : W) ^ i * F (b i) ^ p ^ (k - i) := by
    rw [Function.iterate_succ_apply', hk]
    simp only [map_sum, map_mul, map_pow, map_natCast]
  have hdvd : (p : W) ^ (k + 1) ∣
      (F^[k + 1]) x - ∑ i ∈ range (k + 1), (p : W) ^ i * b i ^ p ^ (k + 1 - i) := by
    rw [hk1, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun i hi => ?_
    have hi' : i ≤ k := by simp at hi; omega
    obtain ⟨y, hy⟩ := hF (b i)
    have h1 : (p : W) ∣ F (b i) - b i ^ p := ⟨y, by rw [hy]; ring⟩
    have h2 := dvd_sub_pow_of_dvd_sub h1 (k - i)
    rw [← pow_mul, ← pow_succ'] at h2
    have e : k + 1 - i = k - i + 1 := by omega
    rw [e, ← mul_sub, show (p : W) ^ (k + 1) = (p : W) ^ i * (p : W) ^ (k - i + 1) by
      rw [← pow_add]; congr 1; omega]
    exact mul_dvd_mul_left _ h2
  obtain ⟨d, hd⟩ := hdvd
  refine ⟨d, ?_⟩
  have hs := ghost_sum_G p Qq F x (k + 1)
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, pow_one] at hs
  have hsum : ∑ i ∈ range (k + 1), (p : Qq) ^ i * (G p Qq F x).coeff i ^ p ^ (k + 1 - i) =
      algebraMap W Qq (∑ i ∈ range (k + 1), (p : W) ^ i * b i ^ p ^ (k + 1 - i)) := by
    simp only [map_sum, map_mul, map_pow, map_natCast]
    exact Finset.sum_congr rfl fun i hi => by rw [hbk i hi]
  rw [hsum] at hs
  have hpk : (p : Qq) ^ (k + 1) ≠ 0 := pow_ne_zero _ (Invertible.ne_zero (p : Qq))
  have key : (p : Qq) ^ (k + 1) * (G p Qq F x).coeff (k + 1) =
      (p : Qq) ^ (k + 1) * algebraMap W Qq d := by
    have e2 : algebraMap W Qq ((F^[k + 1]) x -
        ∑ i ∈ range (k + 1), (p : W) ^ i * b i ^ p ^ (k + 1 - i)) =
        (p : Qq) ^ (k + 1) * algebraMap W Qq d := by
      rw [hd, map_mul, map_pow, map_natCast]
    rw [← e2, map_sub, ← hs]
    ring
  exact mul_left_cancel₀ hpk key
def sFun (hinj : Function.Injective (algebraMap W Qq)) (x : W) : WittVector p W :=
  WittVector.mk p fun n => (G_coeff_integral p Qq F hF hinj x n).choose
theorem map_sFun (hinj : Function.Injective (algebraMap W Qq)) (x : W) :
    WittVector.map (algebraMap W Qq) (sFun p Qq F hF hinj x) = G p Qq F x := by
  ext n
  rw [WittVector.map_coeff]
  exact (G_coeff_integral p Qq F hF hinj x n).choose_spec.symm
def sHom (hinj : Function.Injective (algebraMap W Qq)) : W →+* WittVector p W where
  toFun := sFun p Qq F hF hinj
  map_one' := map_injective _ hinj (by rw [map_sFun, map_one, G_one])
  map_mul' x y := map_injective _ hinj (by rw [map_mul, map_sFun, map_sFun, map_sFun, G_mul])
  map_zero' := map_injective _ hinj (by rw [map_sFun, map_zero, G_zero])
  map_add' x y := map_injective _ hinj (by rw [map_add, map_sFun, map_sFun, map_sFun, G_add])
end Dwork
end PI.WittUnramWork


