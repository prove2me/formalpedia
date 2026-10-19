-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_exists_differentiable_eq_twistedL_and_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:21:55.305264+00:00
-- url     : https://prove2.me/submissions/eeff9c0c-0245-44b4-ab70-ef0153194d00

import Definitions.Def_ArtinHecke
import Definitions.Def_NumberField_CompletedRayL
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinL_Abelian
import Theorems.Thm_ArtinL_Abelian_exists_narrowRayClassChar_conductor_eq_localValue_u0
import Theorems.Thm_ArtinL_Abelian_dvd_conductor_iff_not_isUnramifiedAt
import Theorems.Thm_PhragmenLindelof_exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip
import Theorems.Thm_LT_HeckeChar_exists_heckeCharOfRayClassChar
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Theorems.Thm_NumberField_TateGlobal_exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_NumberField_exists_completedRayL_functionalEquation_of_primitive
import Definitions.Def_LanglandsTunnell_ArtinFrobenius
import Definitions.Def_ArtinHeckeRowL
import Theorems.Thm_ArtinPrimitiveRoots_heckeLSeries_euler_package_of_le
import Theorems.Thm_NumberField_natCard_sUnit_quotient_range_powMonoidHom
import Mathlib

universe u

section
section
/-! # L3K_Gamma: the Gamma-factor ratio on the left edge of the convexity strip

* `norm_Gamma_mono`: `σ ↦ ‖Γ(σ + it)‖ / Γ(σ)` is nondecreasing on `σ > 0` (Gauss's product).
* `norm_Gamma_one_add_sq`: `‖Γ(1 + it)‖² = π |t| / |sinh(π t)|`.
* `exists_norm_Gammaℂ_ratio_le`: for `0 < δ < 1`,
  `‖Γ_ℂ(1 + δ − it) / Γ_ℂ(−δ + it)‖ ≤ C (1 + |t|)^3`. -/

open Complex Filter Topology

set_option autoImplicit false

namespace ArtinPrimitiveRoots

namespace L3K

lemma norm_GammaSeq (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    ‖GammaSeq s n‖ =
      (n : ℝ) ^ s.re * (Nat.factorial n : ℝ) / ∏ j ∈ Finset.range (n + 1), ‖s + j‖ := by
  rw [GammaSeq, norm_div, norm_mul, norm_prod,
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp

lemma prod_pos_norm {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    0 < ∏ j ∈ Finset.range (n + 1), ‖s + j‖ := by
  refine Finset.prod_pos fun j _ => norm_pos_iff.2 fun h => ?_
  have := congrArg Complex.re h
  simp at this
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

lemma term_ineq {x y t : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ‖(y : ℂ) + t * I‖ * ‖(x : ℂ)‖ ≤ ‖(x : ℂ) + t * I‖ * ‖(y : ℂ)‖ := by
  have hy : 0 < y := hx.trans_le hxy
  rw [Complex.norm_add_mul_I, Complex.norm_add_mul_I, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx, abs_of_pos hy]
  have e1 : √(y ^ 2 + t ^ 2) * x = √((y ^ 2 + t ^ 2) * x ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hx.le]
  have e2 : √(x ^ 2 + t ^ 2) * y = √((x ^ 2 + t ^ 2) * y ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hy.le]
  rw [e1, e2]
  apply Real.sqrt_le_sqrt
  have h1 : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx.le hxy 2
  nlinarith [sq_nonneg t]

/-- `‖Γ(a + it)‖ Γ(b) ≤ ‖Γ(b + it)‖ Γ(a)` for `0 < a ≤ b`. -/
theorem norm_Gamma_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (t : ℝ) :
    ‖Gamma ((a : ℂ) + t * I)‖ * ‖Gamma (b : ℂ)‖ ≤ ‖Gamma ((b : ℂ) + t * I)‖ * ‖Gamma (a : ℂ)‖ := by
  have hb : 0 < b := ha.trans_le hab
  have key : ∀ n : ℕ, n ≠ 0 →
      ‖GammaSeq ((a : ℂ) + t * I) n‖ * ‖GammaSeq (b : ℂ) n‖ ≤
        ‖GammaSeq ((b : ℂ) + t * I) n‖ * ‖GammaSeq (a : ℂ) n‖ := by
    intro n hn
    have hre : ∀ x : ℝ, ((x : ℂ) + t * I).re = x := fun x => by simp
    rw [norm_GammaSeq _ hn, norm_GammaSeq _ hn, norm_GammaSeq _ hn, norm_GammaSeq _ hn,
      hre, hre, Complex.ofReal_re, Complex.ofReal_re]
    have hPa := prod_pos_norm (s := (a : ℂ) + t * I) (by rw [hre]; exact ha) n
    have hPb := prod_pos_norm (s := (b : ℂ) + t * I) (by rw [hre]; exact hb) n
    have hQa := prod_pos_norm (s := (a : ℂ)) (by simpa using ha) n
    have hQb := prod_pos_norm (s := (b : ℂ)) (by simpa using hb) n
    rw [div_mul_div_comm, div_mul_div_comm]
    have hnum : (n : ℝ) ^ a * (Nat.factorial n : ℝ) * ((n : ℝ) ^ b * (Nat.factorial n : ℝ)) =
        (n : ℝ) ^ b * (Nat.factorial n : ℝ) * ((n : ℝ) ^ a * (Nat.factorial n : ℝ)) := by ring
    rw [hnum]
    apply div_le_div_of_nonneg_left (by positivity) (mul_pos hPb hQa)
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun j _ => by positivity)
    intro j _
    have e1 : ∀ x : ℝ, (x : ℂ) + t * I + j = ((x + j : ℝ) : ℂ) + t * I := fun x => by
      push_cast; ring
    have e2 : ∀ x : ℝ, (x : ℂ) + j = ((x + j : ℝ) : ℂ) := fun x => by push_cast; ring
    rw [e1, e1, e2, e2]
    exact term_ineq (by positivity) (by linarith)
  have hlim : ∀ s : ℂ, Tendsto (fun n => ‖GammaSeq s n‖) atTop (𝓝 ‖Gamma s‖) :=
    fun s => (GammaSeq_tendsto_Gamma s).norm
  exact le_of_tendsto_of_tendsto ((hlim _).mul (hlim _)) ((hlim _).mul (hlim _))
    (by filter_upwards [eventually_ne_atTop 0] with n hn using key n hn)

lemma norm_sin_le (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; congr 1; simp
  have h2 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; congr 1; simp
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
  have h3 : ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ ≤ Real.exp z.im + Real.exp (-z.im) := by
    rw [← h1, ← h2]; exact norm_sub_le _ _
  have h4 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.2 (le_abs_self _)
  have h5 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.2 (neg_le_abs _)
  linarith

/-- `‖Γ(1 + it)‖² ‖sin(π(1 + it))‖ = π |t|`. -/
lemma norm_Gamma_one_add_sq_mul (t : ℝ) :
    ‖Gamma (1 + t * I)‖ ^ 2 * ‖Complex.sin ((Real.pi : ℂ) * (1 + t * I))‖ = Real.pi * |t| := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have hz : (-(t : ℂ) * I) ≠ 0 := by
    simp [ht]
  have hrefl := Gamma_mul_Gamma_one_sub (1 + t * I)
  have hsub : (1 : ℂ) - (1 + t * I) = -(t : ℂ) * I := by ring
  rw [hsub] at hrefl
  have hconj : Gamma (1 - t * I) = (starRingEnd ℂ) (Gamma (1 + t * I)) := by
    rw [← Gamma_conj]; congr 1; simp [Complex.conj_ofReal]; ring
  have hadd : Gamma (1 - t * I) = (-(t : ℂ) * I) * Gamma (-(t : ℂ) * I) := by
    have := Gamma_add_one (-(t : ℂ) * I) hz
    rw [show -(t : ℂ) * I + 1 = 1 - t * I by ring] at this
    exact this
  have hsq : (‖Gamma (1 + t * I)‖ ^ 2 : ℂ) = Gamma (1 + t * I) * Gamma (1 - t * I) := by
    rw [hconj, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hsin : Complex.sin ((Real.pi : ℂ) * (1 + t * I)) ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hrefl
    rcases mul_eq_zero.1 hrefl with h | h
    · exact Gamma_ne_zero_of_re_pos (by simp) h
    · exact Gamma_ne_zero (fun m hm => by
        have := congrArg Complex.re hm; simp at this
        have := congrArg Complex.im hm; simp at this; exact ht this) h
  have key : (‖Gamma (1 + t * I)‖ ^ 2 : ℂ) * Complex.sin ((Real.pi : ℂ) * (1 + t * I)) =
      (-(t : ℂ) * I) * Real.pi := by
    rw [hsq, hadd, show Gamma (1 + t * I) * (-(t : ℂ) * I * Gamma (-(t : ℂ) * I)) =
      (-(t : ℂ) * I) * (Gamma (1 + t * I) * Gamma (-(t : ℂ) * I)) by ring, hrefl]
    field_simp
  have := congrArg (‖·‖) key
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_neg,
    Complex.norm_I, mul_one, abs_norm] at this
  rw [this, abs_of_pos Real.pi_pos]; ring

lemma norm_sin_pi_one_add (t : ℝ) :
    ‖Complex.sin ((Real.pi : ℂ) * (1 + t * I))‖ = |Real.sinh (Real.pi * t)| := by
  rw [show (Real.pi : ℂ) * (1 + t * I) = ((Real.pi * t : ℝ) : ℂ) * I + Real.pi by push_cast; ring,
    Complex.sin_add_pi, norm_neg, Complex.sin_mul_I, norm_mul, Complex.norm_I, mul_one,
    ← Complex.ofReal_sinh, Complex.norm_real, Real.norm_eq_abs]

/-- `‖Γ(1 + it)‖² ≤ 4π e^π (1 + |t|) e^{−π|t|}`. -/
lemma norm_Gamma_one_add_sq_le (t : ℝ) :
    ‖Gamma (1 + t * I)‖ ^ 2 ≤ 4 * Real.pi * Real.exp Real.pi * (1 + |t|) * Real.exp (-(Real.pi * |t|)) := by
  have hk := norm_Gamma_one_add_sq_mul t
  rw [norm_sin_pi_one_add] at hk
  have hsh : |Real.sinh (Real.pi * t)| = Real.sinh (Real.pi * |t|) := by
    rw [Real.abs_sinh, abs_mul, abs_of_pos Real.pi_pos]
  rw [hsh] at hk
  set G := ‖Gamma (1 + t * I)‖ ^ 2 with hG
  set x := Real.pi * |t| with hx
  have hpi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hx0 : 0 ≤ x := by positivity
  have hG0 : 0 ≤ G := by positivity
  have hE : 1 ≤ Real.exp Real.pi := Real.one_le_exp hpi.le
  have hRHS : 4 * Real.pi * (1 + |t|) * Real.exp (-x) ≤
      4 * Real.pi * Real.exp Real.pi * (1 + |t|) * Real.exp (-x) := by
    have : 0 ≤ 4 * Real.pi * (1 + |t|) * Real.exp (-x) := by positivity
    nlinarith
  rcases eq_or_lt_of_le hx0 with h0 | hpos
  · have ht : t = 0 := by
      have : |t| = 0 := by
        rcases mul_eq_zero.1 h0.symm with h | h
        · exact absurd h hpi.ne'
        · exact h
      exact abs_eq_zero.1 this
    subst ht
    have : G = 1 := by rw [hG]; simp
    rw [this, ← h0, abs_zero, add_zero, neg_zero, Real.exp_zero, mul_one, mul_one]
    nlinarith
  have hsx : 0 < Real.sinh x := Real.sinh_pos_iff.2 hpos
  have hGeq : G = x / Real.sinh x := by field_simp; linarith
  rcases le_or_gt Real.pi x with hbig | hsmall
  · -- `sinh x ≥ e^x / 4`
    have hex : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
    have hemx : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hsh4 : Real.exp x / 4 ≤ Real.sinh x := by
      rw [Real.sinh_eq]; linarith
    have hprod : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    have hG4 : G ≤ 4 * x * Real.exp (-x) := by
      rw [hGeq, div_le_iff₀ hsx]
      have h1 : 4 * x * Real.exp (-x) * (Real.exp x / 4) = x := by
        field_simp
        rw [mul_comm]; exact hprod
      have : 0 ≤ 4 * x * Real.exp (-x) := by positivity
      nlinarith
    refine hG4.trans (le_trans ?_ hRHS)
    have : x ≤ Real.pi * (1 + |t|) := by rw [hx]; nlinarith [abs_nonneg t]
    have he := Real.exp_pos (-x)
    nlinarith
  · have hG1 : G ≤ 1 := by
      rw [hGeq, div_le_one hsx]; exact Real.self_le_sinh_iff.2 hx0
    refine hG1.trans ?_
    have hex : Real.exp (-Real.pi) ≤ Real.exp (-x) := Real.exp_le_exp.2 (by linarith)
    have hep : Real.exp Real.pi * Real.exp (-Real.pi) = 1 := by rw [← Real.exp_add]; simp
    have : 1 ≤ 4 * Real.pi * (1 + |t|) * Real.exp (-x) * Real.exp Real.pi := by
      have h1 : 1 ≤ 4 * Real.pi * (1 + |t|) := by nlinarith [abs_nonneg t]
      have h2 : 1 ≤ Real.exp (-x) * Real.exp Real.pi := by nlinarith [Real.exp_pos (-Real.pi)]
      nlinarith [Real.exp_pos (-x)]
    have e : 4 * Real.pi * Real.exp Real.pi * (1 + |t|) * Real.exp (-x) =
        4 * Real.pi * (1 + |t|) * Real.exp (-x) * Real.exp Real.pi := by ring
    linarith

/-- The left-edge Gamma ratio: `‖Γ(1 + δ − it) / Γ(−δ + it)‖ ≤ 4 e^π Γ(1+δ)² (1 + |t|)³`. -/
theorem norm_Gamma_ratio_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (t : ℝ) :
    ‖Gamma (1 + δ - t * I) / Gamma (-δ + t * I)‖ ≤
      4 * Real.exp Real.pi * Real.Gamma (1 + δ) ^ 2 * (1 + |t|) ^ 3 := by
  set s : ℂ := -δ + t * I with hs
  have h1s : (1 : ℂ) + δ - t * I = 1 - s := by rw [hs]; ring
  rw [h1s]
  have hrefl := Gamma_mul_Gamma_one_sub s
  have hΓs : Gamma s ≠ 0 := Gamma_ne_zero fun m hm => by
    have := congrArg Complex.re hm
    simp [hs] at this
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at this; linarith
    · have : (1 : ℝ) ≤ m := by exact_mod_cast h
      linarith
  have hΓ1s : Gamma (1 - s) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp [hs]; linarith)
  have hsin : Complex.sin (Real.pi * s) ≠ 0 := by
    intro h0; rw [h0, div_zero] at hrefl; exact mul_ne_zero hΓs hΓ1s hrefl
  have hratio : Gamma (1 - s) / Gamma s = Gamma (1 - s) ^ 2 * Complex.sin (Real.pi * s) / Real.pi := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    rw [eq_div_iff hsin] at hrefl
    rw [div_eq_iff hΓs, div_mul_eq_mul_div, eq_div_iff hpi]
    linear_combination (-(Gamma (1 - s))) * hrefl
  rw [hratio, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  -- `‖Γ(1 − s)‖ = ‖Γ(1 + δ + it)‖`
  have hconj : ‖Gamma (1 - s)‖ = ‖Gamma (((1 + δ : ℝ) : ℂ) + t * I)‖ := by
    rw [show 1 - s = (starRingEnd ℂ) (((1 + δ : ℝ) : ℂ) + t * I) by
      rw [hs]; simp [Complex.conj_ofReal]; ring, Gamma_conj, Complex.norm_conj]
  have hmono := norm_Gamma_mono (a := 1 + δ) (b := 2) (by linarith) (by linarith) t
  have h2 : ‖Gamma ((2 : ℝ) : ℂ)‖ = 1 := by
    rw [show ((2 : ℝ) : ℂ) = 1 + 1 by norm_num, Gamma_add_one _ one_ne_zero, Gamma_one]; simp
  have h2t : Gamma (((2 : ℝ) : ℂ) + t * I) = (1 + t * I) * Gamma (1 + t * I) := by
    rw [show ((2 : ℝ) : ℂ) + t * I = (1 + t * I) + 1 by push_cast; ring]
    exact Gamma_add_one _ (fun h => by have := congrArg Complex.re h; simp at this)
  have hGr : ‖Gamma (((1 + δ : ℝ) : ℂ))‖ = Real.Gamma (1 + δ) := by
    rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.Gamma_pos_of_pos (by linarith))]
  rw [h2, mul_one, h2t, norm_mul, hGr] at hmono
  have hnorm1 : ‖(1 : ℂ) + t * I‖ ^ 2 = 1 + t ^ 2 := by
    rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by simp, Complex.norm_add_mul_I,
      Real.sq_sqrt (by positivity)]; ring
  have hG1 := norm_Gamma_one_add_sq_le t
  have hsinb : ‖Complex.sin (Real.pi * s)‖ ≤ Real.exp (Real.pi * |t|) := by
    refine (norm_sin_le _).trans (le_of_eq ?_)
    congr 1
    rw [hs]; simp [abs_mul, abs_of_pos Real.pi_pos]
  set g := ‖Gamma (((1 + δ : ℝ) : ℂ) + t * I)‖
  set A := ‖Gamma (1 + t * I)‖
  set R := Real.Gamma (1 + δ)
  have hR : 0 < R := Real.Gamma_pos_of_pos (by linarith)
  have hg0 : 0 ≤ g := norm_nonneg _
  have hgsq : g ^ 2 ≤ R ^ 2 * ((1 + t ^ 2) * A ^ 2) := by
    have : g ≤ ‖(1 : ℂ) + t * I‖ * A * R := hmono
    have h' : g ^ 2 ≤ (‖(1 : ℂ) + t * I‖ * A * R) ^ 2 := pow_le_pow_left₀ hg0 this 2
    calc g ^ 2 ≤ (‖(1 : ℂ) + t * I‖ * A * R) ^ 2 := h'
      _ = R ^ 2 * (‖(1 : ℂ) + t * I‖ ^ 2 * A ^ 2) := by ring
      _ = R ^ 2 * ((1 + t ^ 2) * A ^ 2) := by rw [hnorm1]
  rw [hconj, div_le_iff₀ Real.pi_pos]
  have hexp : Real.exp (-(Real.pi * |t|)) * Real.exp (Real.pi * |t|) = 1 := by
    rw [← Real.exp_add]; simp
  have hA2 : A ^ 2 * Real.exp (Real.pi * |t|) ≤ 4 * Real.pi * Real.exp Real.pi * (1 + |t|) := by
    have := mul_le_mul_of_nonneg_right hG1 (Real.exp_pos (Real.pi * |t|)).le
    calc A ^ 2 * Real.exp (Real.pi * |t|)
        ≤ 4 * Real.pi * Real.exp Real.pi * (1 + |t|) * Real.exp (-(Real.pi * |t|)) *
            Real.exp (Real.pi * |t|) := this
      _ = 4 * Real.pi * Real.exp Real.pi * (1 + |t|) := by rw [mul_assoc _ (Real.exp _), hexp, mul_one]
  have ht2 : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  have hsin0 := norm_nonneg (Complex.sin (Real.pi * s))
  calc g ^ 2 * ‖Complex.sin (Real.pi * s)‖
      ≤ R ^ 2 * ((1 + t ^ 2) * A ^ 2) * Real.exp (Real.pi * |t|) :=
        mul_le_mul hgsq hsinb hsin0 (by positivity)
    _ = R ^ 2 * (1 + t ^ 2) * (A ^ 2 * Real.exp (Real.pi * |t|)) := by ring
    _ ≤ R ^ 2 * (1 + |t|) ^ 2 * (4 * Real.pi * Real.exp Real.pi * (1 + |t|)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left ht2 (by positivity)) hA2 (by positivity)
          (by positivity)
    _ = 4 * Real.exp Real.pi * R ^ 2 * (1 + |t|) ^ 3 * Real.pi := by ring

end L3K

end ArtinPrimitiveRoots

end
end

section
section
/-! # T12A_Sum: Dirichlet series over ideals as sums over ideals

For `f : Ideal (𝓞 K) → ℂ` bounded by `1` and `Re s > 1`, the `LSeries` whose `n`-th coefficient is
`∑ᶠ I ∈ {absNorm I = n}, f I` is the (absolutely convergent) sum `∑' I, f I * N(I)^{-s}`. -/

set_option maxHeartbeats 4000000
set_option autoImplicit false

open NumberField Complex Filter Topology Ideal

namespace ArtinPrimitiveRoots.T12A

variable {K : Type*} [Field K] [NumberField K]

theorem lseriesSummable_card {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ)) s := by
  have hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 K) // absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue K)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
      fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ))
    (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim))
    (fun _ ↦ Nat.cast_nonneg _) zero_le_one (s := s) hs
  simpa using h

instance finite_fiber (n : ℕ) : Finite {I : Ideal (𝓞 K) // absNorm I = n} := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton {I : Ideal (𝓞 K) // absNorm I = 0} :=
      ⟨fun a b => Subtype.ext (by
        rw [Ideal.absNorm_eq_zero_iff.mp a.2, Ideal.absNorm_eq_zero_iff.mp b.2])⟩
    exact Finite.of_subsingleton
  · exact (finite_setOfPred_absNorm_eq n).to_subtype

end ArtinPrimitiveRoots.T12A

end
end

section
section
/-! # T12A_Ray: a `HeckeChar` as a narrow ray class character

A `HeckeChar K 𝔪` (𝔪 ≠ ⊥) is `I ↦ ψ([I])` on ideals coprime to `𝔪` for a character `ψ` of the narrow
ray class group mod `𝔪` with parity set `∅`, and `χ.LSeries = rayClassLSeries ψ` on `Re s > 1`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply nonZeroDivisors Complex

namespace ArtinPrimitiveRoots.T12A

section Coprime

variable {F : Type*} [Field F] [NumberField F]

theorem sup_eq_top_iff_forall {I 𝔣 : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    I ⊔ 𝔣 = ⊤ ↔ ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ 𝔣 → ¬ v.asIdeal ∣ I := by
  constructor
  · intro h v hf hI'
    apply v.isPrime.ne_top
    rw [eq_top_iff, ← h]
    exact sup_le (Ideal.le_of_dvd hI') (Ideal.le_of_dvd hf)
  · intro h
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hmb : m ≠ ⊥ := by
      intro hb
      apply hI
      rw [eq_bot_iff, ← hb]
      exact le_trans le_sup_left hle
    let v : HeightOneSpectrum (𝓞 F) := ⟨m, hm.isPrime, hmb⟩
    exact h v (Ideal.dvd_iff_le.mpr (le_trans le_sup_right hle))
      (Ideal.dvd_iff_le.mpr (le_trans le_sup_left hle))

theorem mk0_mem_coprimeToModulus_iff {I 𝔣 : Ideal (𝓞 F)} (hI : I ∈ (Ideal (𝓞 F))⁰) :
    FractionalIdeal.mk0 F ⟨I, hI⟩ ∈ coprimeToModulus F 𝔣 ↔ I ⊔ 𝔣 = ⊤ := by
  have hI0 : I ≠ 0 := nonZeroDivisors.ne_zero hI
  rw [mem_coprimeToModulus_iff, sup_eq_top_iff_forall hI0]
  refine forall_congr' fun v => imp_congr_right fun _ => ?_
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.count_coe F v hI0, Nat.cast_eq_zero]
  constructor
  · intro h hd
    exact (Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mpr hd h
  · intro h
    by_contra hc
    exact h ((Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mp hc)

theorem span_ne_bot {α : 𝓞 F} (hα : α ≠ 0) : Ideal.span {α} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact hα

theorem span_sup_eq_top {𝔣 : Ideal (𝓞 F)} {α : 𝓞 F} (h1 : α - 1 ∈ 𝔣) :
    Ideal.span {α} ⊔ 𝔣 = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h : (1 : 𝓞 F) = α - (α - 1) := by ring
  rw [h]
  exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self α))
    (Ideal.mem_sup_right h1)

end Coprime

section Factor

variable {F : Type*} [Field F] [NumberField F] {𝔣 : Ideal (𝓞 F)}

theorem hasFiniteMulSupport_pow_count (f : HeightOneSpectrum (𝓞 F) → ℂ) {I : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      f v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  by_contra hd
  apply hv
  have : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0 := by
    by_contra hc
    exact hd ((Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hc)
  simp only [this, pow_zero]

open Classical in
theorem count_prime_eq (v w : HeightOneSpectrum (𝓞 F)) :
    (Associates.mk v.asIdeal).count (Associates.mk w.asIdeal).factors = if v = w then 1 else 0 := by
  split_ifs with h
  · subst h
    exact Associates.count_self v.associates_irreducible
  · by_contra hc
    have hd := (Associates.count_ne_zero_iff_dvd w.ne_bot v.irreducible).mp hc
    apply h
    exact HeightOneSpectrum.ext
      ((w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.le_of_dvd hd)).symm)

/-- A `HeckeChar` is determined on nonzero ideals by its values at primes. -/
theorem heckeChar_eq_finprod (η : ArtinPrimitiveRoots.HeckeChar F 𝔣)
    (f : HeightOneSpectrum (𝓞 F) → ℂ) (hf : ∀ v : HeightOneSpectrum (𝓞 F), η.toFun v.asIdeal = f v)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    η.toFun I = ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      f v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
  revert hI
  refine UniqueFactorizationMonoid.induction_on_prime I ?_ ?_ ?_
  · intro h
    exact absurd rfl h
  · intro x hx _
    rw [Ideal.isUnit_iff] at hx
    subst hx
    have h1 : η.toFun ⊤ = 1 := by
      have := η.map_principal' 1 one_ne_zero (by rw [sub_self]; exact Ideal.zero_mem _)
      rwa [Ideal.span_singleton_one] at this
    rw [h1, ← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one]
    exact (finprod_eq_one_of_forall_eq_one fun v => by
      rw [Associates.count_zero v.associates_irreducible, pow_zero]).symm
  · intro a p ha hp ih hpa
    have ha' : a ≠ ⊥ := ha
    let v₀ : HeightOneSpectrum (𝓞 F) := HeightOneSpectrum.ofPrime hp
    have hp0 : p ≠ 0 := hp.ne_zero
    rw [η.map_mul', ih ha']
    have hcount : ∀ v : HeightOneSpectrum (𝓞 F),
        (Associates.mk v.asIdeal).count (Associates.mk (p * a)).factors =
          (Associates.mk v.asIdeal).count (Associates.mk p).factors +
            (Associates.mk v.asIdeal).count (Associates.mk a).factors := by
      intro v
      rw [← Associates.mk_mul_mk]
      exact Associates.count_mul (Associates.mk_ne_zero.mpr hp0) (Associates.mk_ne_zero.mpr ha)
        v.associates_irreducible
    simp_rw [hcount, pow_add]
    rw [finprod_mul_distrib (hasFiniteMulSupport_pow_count f (I := p) hp0)
      (hasFiniteMulSupport_pow_count f ha')]
    congr 1
    have hp' : p = v₀.asIdeal := rfl
    rw [hp', hf v₀, finprod_eq_single _ v₀]
    · rw [count_prime_eq, if_pos rfl, pow_one]
    · intro v hv
      rw [count_prime_eq, if_neg hv, pow_zero]

end Factor

section Ray

variable {K : Type} [Field K] [NumberField K] {𝔪 : Ideal (𝓞 K)}

theorem heckeChar_ne_zero (χ : HeckeChar K 𝔪) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (hc : I ⊔ 𝔪 = ⊤) : χ.toFun I ≠ 0 := by
  rw [Ne, χ.eq_zero_iff']
  tauto

theorem heckeChar_eq_zero (χ : HeckeChar K 𝔪) {I : Ideal (𝓞 K)}
    (h : ¬ (I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤)) : χ.toFun I = 0 := by
  rw [χ.eq_zero_iff']
  tauto

open Classical in
/-- The values of `χ` at primes, as units (`1` at primes dividing `𝔪`). -/
noncomputable def primeVal (χ : HeckeChar K 𝔪) (v : HeightOneSpectrum (𝓞 K)) : ℂˣ :=
  if h : v.asIdeal ⊔ 𝔪 = ⊤ then Units.mk0 (χ.toFun v.asIdeal) (heckeChar_ne_zero χ v.ne_bot h)
  else 1

theorem raySymbol_coe (χ : HeckeChar K 𝔪) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hc : I ⊔ 𝔪 = ⊤) :
    ((raySymbol K (primeVal χ) (I : FractionalIdeal (𝓞 K)⁰ K) : ℂˣ) : ℂ) = χ.toFun I := by
  rw [heckeChar_eq_finprod χ (fun v => χ.toFun v.asIdeal) (fun v => rfl) I hI, raySymbol,
    ← Units.coeHom_apply, MonoidHom.map_finprod _ (hasFiniteMulSupport_raySymbol_factors K _ _)]
  refine finprod_congr fun v => ?_
  rw [FractionalIdeal.count_coe K v hI, zpow_natCast, Units.coeHom_apply, Units.val_pow_eq_pow_val]
  by_cases hd : v.asIdeal ∣ I
  · have hv : v.asIdeal ⊔ 𝔪 = ⊤ :=
      eq_top_iff.mpr (hc ▸ sup_le_sup_right (Ideal.le_of_dvd hd) _)
    rw [primeVal, dif_pos hv, Units.val_mk0]
  · have : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0 := by
      by_contra h0
      exact hd ((Associates.count_ne_zero_iff_dvd hI v.irreducible).mp h0)
    rw [this, pow_zero, pow_zero]

theorem hkill (χ : HeckeChar K 𝔪) : ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔪 →
    (∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) →
    raySymbol K (primeVal χ) ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 1 := by
  intro α hα h1 _
  apply Units.ext
  rw [raySymbol_coe χ (span_ne_bot hα) (span_sup_eq_top h1), Units.val_one]
  exact χ.map_principal' α hα h1

/-- The narrow ray class character attached to `χ`. -/
noncomputable def rayChar (χ : HeckeChar K 𝔪) : NarrowRayClassGroup K 𝔪 →* ℂ :=
  (Units.coeHom ℂ).comp (raySymbolDescend K (primeVal χ) (hkill χ))

theorem rayChar_mk (χ : HeckeChar K 𝔪) (y : ↥(coprimeToModulus K 𝔪)) :
    rayChar χ (NarrowRayClassGroup.mk K 𝔪 y) =
      ((raySymbol K (primeVal χ)
        ((y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) : ℂˣ) : ℂ) := by
  rw [rayChar, MonoidHom.comp_apply, raySymbolDescend_mk, raySymbolHom_apply, Units.coeHom_apply]

theorem rayChar_mk_ideal (χ : HeckeChar K 𝔪) {I : Ideal (𝓞 K)} (hI : I ∈ (Ideal (𝓞 K))⁰)
    (hc : FractionalIdeal.mk0 K ⟨I, hI⟩ ∈ coprimeToModulus K 𝔪) :
    rayChar χ (NarrowRayClassGroup.mk K 𝔪 ⟨FractionalIdeal.mk0 K ⟨I, hI⟩, hc⟩) = χ.toFun I := by
  rw [rayChar_mk]
  show ((raySymbol K (primeVal χ) ((FractionalIdeal.mk0 K ⟨I, hI⟩ :
    (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) : ℂˣ) : ℂ) = _
  rw [FractionalIdeal.coe_mk0]
  exact raySymbol_coe χ (nonZeroDivisors.ne_zero hI) ((mk0_mem_coprimeToModulus_iff hI).1 hc)

theorem norm_rayChar (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar K 𝔪) (C : NarrowRayClassGroup K 𝔪) :
    ‖rayChar χ C‖ = 1 := by
  haveI := Deep.NTSupply.finite K h𝔪
  have h : rayChar χ C ^ Nat.card (NarrowRayClassGroup K 𝔪) = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  exact norm_eq_one_of_pow_eq_one h Nat.card_pos.ne'

open Classical in
/-- The class of an ideal (`1` when it is zero or not coprime to `𝔪`). -/
noncomputable def cls (𝔪 : Ideal (𝓞 K)) (I : Ideal (𝓞 K)) : NarrowRayClassGroup K 𝔪 :=
  if h : I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤ then
    NarrowRayClassGroup.mk K 𝔪 ⟨FractionalIdeal.mk0 K ⟨I, mem_nonZeroDivisors_of_ne_zero h.1⟩,
      (mk0_mem_coprimeToModulus_iff _).2 h.2⟩
  else 1

open Classical in
theorem heckeChar_eq_ite (χ : HeckeChar K 𝔪) (I : Ideal (𝓞 K)) :
    χ.toFun I = if I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤ then rayChar χ (cls 𝔪 I) else 0 := by
  split_ifs with h
  · rw [cls, dif_pos h, rayChar_mk_ideal]
  · exact heckeChar_eq_zero χ h

theorem norm_heckeChar_le (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar K 𝔪) (I : Ideal (𝓞 K)) :
    ‖χ.toFun I‖ ≤ 1 := by
  rw [heckeChar_eq_ite]
  split_ifs
  · rw [norm_rayChar h𝔪]
  · simp

open Classical in
theorem rayZetaCoeff_eq (C : NarrowRayClassGroup K 𝔪) {n : ℕ} (hn : n ≠ 0) :
    M4aTorus.rayZetaCoeff K 𝔪 C n =
      ((Ideal.finite_setOfPred_absNorm_eq n).toFinset.filter
        (fun I => (I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤) ∧ cls 𝔪 I = C)).card := by
  rw [M4aTorus.rayZetaCoeff, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1.1, ?_⟩
      invFun := fun y => ⟨⟨y.1, mem_nonZeroDivisors_of_ne_zero ?_⟩, ?_⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  · obtain ⟨⟨I, hI⟩, hn', hc, hC⟩ := x
    have hcop := (mk0_mem_coprimeToModulus_iff hI).1 hc
    have hgood : I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤ := ⟨nonZeroDivisors.ne_zero hI, hcop⟩
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    refine ⟨hn', hgood, ?_⟩
    rw [cls, dif_pos hgood]
    exact hC
  · have h := y.2
    rw [Finset.mem_filter] at h
    exact h.2.1.1
  · have h := y.2
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at h
    refine ⟨h.1, (mk0_mem_coprimeToModulus_iff _).2 h.2.1.2, ?_⟩
    have hC := h.2.2
    rw [cls, dif_pos h.2.1] at hC
    exact hC

open Classical in
theorem coeff_sum (χ : HeckeChar K 𝔪) [Fintype (NarrowRayClassGroup K 𝔪)] {n : ℕ} (hn : n ≠ 0) :
    ∑ C, rayChar χ C * (M4aTorus.rayZetaCoeff K 𝔪 C n : ℂ) = χ.coeff n := by
  set S := (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).toFinset
  have h1 : ∀ C, rayChar χ C * (M4aTorus.rayZetaCoeff K 𝔪 C n : ℂ) =
      ∑ I ∈ (S.filter (fun I => I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤)).filter (fun I => cls 𝔪 I = C),
        rayChar χ (cls 𝔪 I) := by
    intro C
    rw [rayZetaCoeff_eq C hn, Finset.filter_filter]
    rw [Finset.sum_congr rfl (g := fun _ => rayChar χ C) (fun I hI => by
      rw [(Finset.mem_filter.mp hI).2.2]), Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [Finset.sum_congr rfl (fun C _ => h1 C), Finset.sum_fiberwise, HeckeChar.coeff,
    finsum_mem_eq_finite_toFinset_sum _ (Ideal.finite_setOfPred_absNorm_eq n),
    Finset.sum_filter]
  exact Finset.sum_congr rfl fun I _ => (heckeChar_eq_ite χ I).symm

open Classical in
theorem lseriesSummable_rayZetaCoeff (C : NarrowRayClassGroup K 𝔪) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (M4aTorus.rayZetaCoeff K 𝔪 C n : ℂ)) s := by
  refine Summable.of_norm_bounded (lseriesSummable_card (K := K) hs).norm fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  refine LSeries.norm_term_le s ?_
  rw [norm_natCast, norm_natCast, Nat.cast_le, rayZetaCoeff_eq C hn.ne']
  have hc : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} =
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).toFinset.card :=
    Nat.card_eq_card_finite_toFinset (Ideal.finite_setOfPred_absNorm_eq n)
  rw [hc]
  exact Finset.card_filter_le _ _

theorem rayClassLSeries_eq (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar K 𝔪) {s : ℂ} (hs : 1 < s.re) :
    M4aTorus.rayClassLSeries K 𝔪 (rayChar χ) s = χ.LSeries s := by
  haveI := Deep.NTSupply.finite K h𝔪
  letI : Fintype (NarrowRayClassGroup K 𝔪) := Fintype.ofFinite _
  classical
  rw [M4aTorus.rayClassLSeries, tsum_fintype]
  simp_rw [M4aTorus.rayZeta, ← LSeries_smul]
  rw [← LSeries_sum (fun C _ => (lseriesSummable_rayZetaCoeff C hs).smul _), HeckeChar.LSeries]
  refine LSeries_congr (fun {n} hn => ?_) s
  rw [Finset.sum_apply]
  simp_rw [Pi.smul_apply, smul_eq_mul]
  exact coeff_sum χ hn

end Ray

end ArtinPrimitiveRoots.T12A

end
end

section
section
/-! # C3A_Sieve: Euler products of multiplicative functions of four ideals

A function `f` on 4-tuples of ideals of `𝓞 F`, supported on exterior tuples, with
`f (P^e · y) = A P e · f y` for exterior primes `P` and exterior `y` prime to `P`, and absolutely
summable, has the Euler product `∑' f = ∏'_P ∑'_e A P e` over the exterior primes (`euler4`).
Proof: the finite sieve `∑' f = (∏_{P ∈ T} L_P) · ∑'_{x prime to T} f x` (induction on `T`) and a
tail estimate. Also a bound `‖f‖ ≤ B` for multiplicative majorants (`norm_le_of_mul`). -/

open NumberField Filter Topology

namespace ArtinPrimitiveRoots

namespace C3A

variable {F : Type*} [Field F] [NumberField F]

/-- 4-tuples of ideals. -/
abbrev Tup (F : Type*) [Field F] [NumberField F] : Type _ :=
  Ideal (𝓞 F) × Ideal (𝓞 F) × Ideal (𝓞 F) × Ideal (𝓞 F)

/-- Exponent vectors. -/
abbrev Exps : Type := ℕ × ℕ × ℕ × ℕ

/-- `P^e · x`, coordinatewise. -/
def pw (P : Ideal (𝓞 F)) (e : Exps) (x : Tup F) : Tup F :=
  (P ^ e.1 * x.1, P ^ e.2.1 * x.2.1, P ^ e.2.2.1 * x.2.2.1, P ^ e.2.2.2 * x.2.2.2)

/-- The unit tuple. -/
def one4 : Tup F := (⊤, ⊤, ⊤, ⊤)

/-- Exterior tuples. -/
def Om (𝔪 : Ideal (𝓞 F)) : Set (Tup F) :=
  {x | IsExterior 𝔪 x.1 ∧ IsExterior 𝔪 x.2.1 ∧ IsExterior 𝔪 x.2.2.1 ∧ IsExterior 𝔪 x.2.2.2}

/-- Tuples prime to `P`. -/
def CopP (P : Ideal (𝓞 F)) : Set (Tup F) :=
  {x | ¬ x.1 ≤ P ∧ ¬ x.2.1 ≤ P ∧ ¬ x.2.2.1 ≤ P ∧ ¬ x.2.2.2 ≤ P}

/-- Tuples prime to every member of `T`. -/
def Cop (T : Finset (Ideal (𝓞 F))) : Set (Tup F) := {x | ∀ P ∈ T, x ∈ CopP P}

/-- Exterior primes. -/
def IsEP (𝔪 P : Ideal (𝓞 F)) : Prop := P.IsPrime ∧ P ≠ ⊥ ∧ P ⊔ 𝔪 = ⊤

/-- The type of exterior primes. -/
abbrev EP (𝔪 : Ideal (𝓞 F)) : Type _ := {P : Ideal (𝓞 F) // P.IsPrime ∧ P ≠ ⊥ ∧ P ⊔ 𝔪 = ⊤}

lemma two_le_absNorm {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    2 ≤ Ideal.absNorm P := by
  have h0 : Ideal.absNorm P ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have h1 : Ideal.absNorm P ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hP.ne_top
  omega

lemma decomp1 {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ∀ I : Ideal (𝓞 F), I ≠ ⊥ → ∃ k J, I = P ^ k * J ∧ ¬ J ≤ P := by
  intro I
  induction hN : Ideal.absNorm I using Nat.strong_induction_on generalizing I with
  | _ N ih =>
  intro hI
  by_cases hle : I ≤ P
  · obtain ⟨J, rfl⟩ := Ideal.dvd_iff_le.2 hle
    have hJ : J ≠ ⊥ := by rintro rfl; exact hI (by simp)
    have hlt : Ideal.absNorm J < N := by
      rw [← hN, map_mul]
      have := two_le_absNorm hP hP0
      have hJ0 : Ideal.absNorm J ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
      have := Nat.pos_of_ne_zero hJ0
      nlinarith
    obtain ⟨k, K, hK, hKP⟩ := ih _ hlt J rfl hJ
    exact ⟨k + 1, K, by rw [hK, pow_succ', mul_assoc], hKP⟩
  · exact ⟨0, I, by simp, hle⟩

lemma cancel1 {P : Ideal (𝓞 F)} (hP0 : P ≠ ⊥) {a b : ℕ} {J J' : Ideal (𝓞 F)}
    (hJ : ¬ J ≤ P) (hJ' : ¬ J' ≤ P) (h : P ^ a * J = P ^ b * J') : a = b ∧ J = J' := by
  have hP : (P : Ideal (𝓞 F)) ≠ 0 := hP0
  have key : ∀ {a b : ℕ} {J J' : Ideal (𝓞 F)}, ¬ J ≤ P → a ≤ b → P ^ a * J = P ^ b * J' →
      a = b ∧ J = J' := by
    intro a b J J' hJ hab h
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add, mul_assoc] at h
    have h2 := mul_left_cancel₀ (pow_ne_zero a hP) h
    rcases c with _ | c
    · simp only [pow_zero, one_mul] at h2
      exact ⟨rfl, h2⟩
    · exfalso; apply hJ; rw [h2, pow_succ', mul_assoc]; exact Ideal.mul_le_left
  rcases le_total a b with hab | hab
  · exact key hJ hab h
  · obtain ⟨h1, h2⟩ := key hJ' hab h.symm
    exact ⟨h1.symm, h2.symm⟩

lemma pw_injective {P : Ideal (𝓞 F)} (hP0 : P ≠ ⊥) {e e' : Exps} {y y' : Tup F}
    (hy : y ∈ CopP P) (hy' : y' ∈ CopP P) (h : pw P e y = pw P e' y') : e = e' ∧ y = y' := by
  obtain ⟨e1, e2, e3, e4⟩ := e
  obtain ⟨e1', e2', e3', e4'⟩ := e'
  obtain ⟨y1, y2, y3, y4⟩ := y
  obtain ⟨y1', y2', y3', y4'⟩ := y'
  simp only [pw, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨a1, a2, a3, a4⟩ := hy
  obtain ⟨b1, b2, b3, b4⟩ := hy'
  obtain ⟨c1, d1⟩ := cancel1 hP0 a1 b1 h1
  obtain ⟨c2, d2⟩ := cancel1 hP0 a2 b2 h2
  obtain ⟨c3, d3⟩ := cancel1 hP0 a3 b3 h3
  obtain ⟨c4, d4⟩ := cancel1 hP0 a4 b4 h4
  subst c1 c2 c3 c4 d1 d2 d3 d4
  exact ⟨rfl, rfl⟩

lemma exterior_of_dvd {𝔪 I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 (J * I)) : IsExterior 𝔪 I := by
  refine ⟨fun h => hI.1 (by rw [h, Ideal.mul_bot]), ?_⟩
  rw [eq_top_iff, ← hI.2]
  exact sup_le_sup_right Ideal.mul_le_right _

lemma mem_Om_of_pw {𝔪 P : Ideal (𝓞 F)} {e : Exps} {y : Tup F} (h : pw P e y ∈ Om 𝔪) :
    y ∈ Om 𝔪 :=
  ⟨exterior_of_dvd h.1, exterior_of_dvd h.2.1, exterior_of_dvd h.2.2.1, exterior_of_dvd h.2.2.2⟩

lemma not_le_pw {P Q I : Ideal (𝓞 F)} (hP : P.IsMaximal) (hQ : Q.IsPrime) (hPQ : P ≠ Q)
    (hI : ¬ I ≤ Q) (k : ℕ) : ¬ P ^ k * I ≤ Q := by
  intro h
  rcases hQ.mul_le.1 h with h1 | h1
  · exact hPQ (hP.eq_of_le hQ.ne_top (hQ.le_of_pow_le h1))
  · exact hI h1

lemma pw_mem_Cop {T : Finset (Ideal (𝓞 F))} (hT : ∀ Q ∈ T, Q.IsPrime) {P : Ideal (𝓞 F)}
    (hP : P.IsMaximal) (hPT : P ∉ T) (e : Exps) {y : Tup F} (hy : y ∈ Cop T) :
    pw P e y ∈ Cop T := by
  intro Q hQ
  have hPQ : P ≠ Q := fun h => hPT (h ▸ hQ)
  obtain ⟨a1, a2, a3, a4⟩ := hy Q hQ
  exact ⟨not_le_pw hP (hT Q hQ) hPQ a1 _, not_le_pw hP (hT Q hQ) hPQ a2 _,
    not_le_pw hP (hT Q hQ) hPQ a3 _, not_le_pw hP (hT Q hQ) hPQ a4 _⟩

lemma isEP_of_le {𝔪 P I : Ideal (𝓞 F)} (hP : P.IsMaximal) (hI : IsExterior 𝔪 I) (hle : I ≤ P) :
    IsEP 𝔪 P := by
  refine ⟨hP.isPrime, fun h => hI.1 (le_bot_iff.1 (h ▸ hle)), ?_⟩
  rw [eq_top_iff, ← hI.2]
  exact sup_le_sup_right hle _

/-- Decomposition of an exterior tuple at a prime. -/
lemma decomp4 {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) {𝔪 : Ideal (𝓞 F)} {x : Tup F}
    (hx : x ∈ Om 𝔪) : ∃ e y, x = pw P e y ∧ y ∈ CopP P := by
  obtain ⟨k1, J1, h1, n1⟩ := decomp1 hP hP0 x.1 hx.1.1
  obtain ⟨k2, J2, h2, n2⟩ := decomp1 hP hP0 x.2.1 hx.2.1.1
  obtain ⟨k3, J3, h3, n3⟩ := decomp1 hP hP0 x.2.2.1 hx.2.2.1.1
  obtain ⟨k4, J4, h4, n4⟩ := decomp1 hP hP0 x.2.2.2 hx.2.2.2.1
  refine ⟨(k1, k2, k3, k4), (J1, J2, J3, J4), ?_, n1, n2, n3, n4⟩
  obtain ⟨x1, x2, x3, x4⟩ := x
  simp only [pw] at *
  rw [← h1, ← h2, ← h3, ← h4]

lemma le_of_pw (P : Ideal (𝓞 F)) (e : Exps) (y : Tup F) :
    (pw P e y).1 ≤ y.1 ∧ (pw P e y).2.1 ≤ y.2.1 ∧ (pw P e y).2.2.1 ≤ y.2.2.1 ∧
      (pw P e y).2.2.2 ≤ y.2.2.2 :=
  ⟨Ideal.mul_le_right, Ideal.mul_le_right, Ideal.mul_le_right, Ideal.mul_le_right⟩

lemma one4_mem_Cop (T : Finset (Ideal (𝓞 F))) (hT : ∀ Q ∈ T, Q.IsPrime) :
    (one4 : Tup F) ∈ Cop T := by
  intro Q hQ
  have : ¬ (⊤ : Ideal (𝓞 F)) ≤ Q := fun h => (hT Q hQ).ne_top (top_le_iff.1 h)
  exact ⟨this, this, this, this⟩

section sieve

variable (𝔪 : Ideal (𝓞 F)) (f : Tup F → ℂ) (A : Ideal (𝓞 F) → Exps → ℂ)

/-- The hypotheses of the Euler product. -/
structure EulerHyp : Prop where
  zero : ∀ x, x ∉ Om 𝔪 → f x = 0
  one : f one4 = 1
  mul : ∀ P, IsEP 𝔪 P → ∀ e y, y ∈ Om 𝔪 → y ∈ CopP P → f (pw P e y) = A P e * f y
  summ : Summable (fun x => ‖f x‖)
  summA : ∀ P, IsEP 𝔪 P → Summable (fun e => ‖A P e‖)

variable {𝔪 f A}

lemma summable_norm_indicator (h : EulerHyp 𝔪 f A) (s : Set (Tup F)) :
    Summable (fun x => ‖s.indicator f x‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => norm_indicator_le_norm_self _ _)
    h.summ

/-- One sieve step. -/
theorem sieve_step (h : EulerHyp 𝔪 f A) (T : Finset (Ideal (𝓞 F))) (hT : ∀ Q ∈ T, Q.IsPrime)
    {P : Ideal (𝓞 F)} (hP : IsEP 𝔪 P) (hPT : P ∉ T) :
    ∑' x, (Cop T).indicator f x =
      (∑' e, A P e) * ∑' x, (Cop (insert P T)).indicator f x := by
  classical
  have hPmax : P.IsMaximal := hP.1.isMaximal hP.2.1
  set h1 := (Cop T).indicator f with hh1
  set h2 := (Cop (insert P T)).indicator f with hh2
  rw [tsum_mul_tsum_of_summable_norm (h.summA P hP) (summable_norm_indicator h _)]
  set G : Exps × Tup F → ℂ := fun z => A P z.1 * h2 z.2 with hG
  -- the key pointwise fact
  have hkey : ∀ z : Exps × Tup F, G z ≠ 0 →
      z.2 ∈ Cop (insert P T) ∧ z.2 ∈ Om 𝔪 ∧ h1 (pw P z.1 z.2) = G z := by
    intro z hz
    have hz2 : h2 z.2 ≠ 0 := fun h0 => hz (by simp [hG, h0])
    have hc : z.2 ∈ Cop (insert P T) := by
      by_contra hc; exact hz2 (Set.indicator_of_notMem hc _)
    have hO : z.2 ∈ Om 𝔪 := by
      by_contra hO; exact hz2 (by rw [hh2, Set.indicator_of_mem hc]; exact h.zero _ hO)
    refine ⟨hc, hO, ?_⟩
    have hcT : z.2 ∈ Cop T := fun Q hQ => hc Q (Finset.mem_insert_of_mem hQ)
    have hcP : z.2 ∈ CopP P := hc P (Finset.mem_insert_self _ _)
    rw [hh1, Set.indicator_of_mem (pw_mem_Cop hT hPmax hPT z.1 hcT), h.mul P hP z.1 z.2 hO hcP,
      hG]
    simp only
    rw [hh2, Set.indicator_of_mem hc]
  refine tsum_eq_tsum_of_ne_zero_bij (fun z => pw P z.1.1 z.1.2) ?_ ?_ ?_
  · rintro ⟨z, hz⟩ ⟨z', hz'⟩ hzz
    have a := (hkey z hz).1 P (Finset.mem_insert_self _ _)
    have b := (hkey z' hz').1 P (Finset.mem_insert_self _ _)
    obtain ⟨he, hy⟩ := pw_injective hP.2.1 a b hzz
    exact Subtype.ext (Prod.ext he hy)
  · intro x hx
    have hx' : h1 x ≠ 0 := hx
    have hxc : x ∈ Cop T := by
      by_contra hc; exact hx' (Set.indicator_of_notMem hc _)
    have hxO : x ∈ Om 𝔪 := by
      by_contra hO; exact hx' (by rw [hh1, Set.indicator_of_mem hxc]; exact h.zero _ hO)
    obtain ⟨e, y, rfl, hyP⟩ := decomp4 hP.1 hP.2.1 hxO
    have hyO : y ∈ Om 𝔪 := mem_Om_of_pw hxO
    have hyc : y ∈ Cop (insert P T) := by
      intro Q hQ
      rcases Finset.mem_insert.1 hQ with rfl | hQ
      · exact hyP
      · obtain ⟨a1, a2, a3, a4⟩ := hxc Q hQ
        obtain ⟨l1, l2, l3, l4⟩ := le_of_pw P e y
        exact ⟨fun h' => a1 (l1.trans h'), fun h' => a2 (l2.trans h'),
          fun h' => a3 (l3.trans h'), fun h' => a4 (l4.trans h')⟩
    have hGe : G (e, y) = h1 (pw P e y) := by
      rw [hh1, Set.indicator_of_mem hxc, h.mul P hP e y hyO hyP, hG]
      simp only
      rw [hh2, Set.indicator_of_mem hyc]
    refine ⟨⟨(e, y), ?_⟩, rfl⟩
    show G (e, y) ≠ 0
    rw [hGe]; exact hx'
  · rintro ⟨z, hz⟩
    exact (hkey z hz).2.2

/-- The finite sieve. -/
theorem sieve_eq (h : EulerHyp 𝔪 f A) (T : Finset (Ideal (𝓞 F))) (hT : ∀ Q ∈ T, IsEP 𝔪 Q) :
    ∑' x, f x = (∏ Q ∈ T, ∑' e, A Q e) * ∑' x, (Cop T).indicator f x := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have : (Cop (∅ : Finset (Ideal (𝓞 F)))) = Set.univ := by
      ext x; simp [Cop]
    rw [this, Set.indicator_univ, Finset.prod_empty, one_mul]
  | insert P T hPT ih =>
    have ih' := ih (fun Q hQ => hT Q (Finset.mem_insert_of_mem hQ))
    rw [ih', sieve_step h T (fun Q hQ => (hT Q (Finset.mem_insert_of_mem hQ)).1)
      (hT P (Finset.mem_insert_self _ _)) hPT, Finset.prod_insert hPT]
    ring

/-- The tail estimate. -/
theorem sieve_tail (h : EulerHyp 𝔪 f A) {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : Finset (EP 𝔪), ∀ T : Finset (EP 𝔪), T₀ ⊆ T →
      ‖∑' x, (Cop (T.map (Function.Embedding.subtype _))).indicator f x - 1‖ < ε := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset (Tup F), ∑' x : {x // x ∉ S}, ‖f x‖ < ε :=
    ((tendsto_tsum_compl_atTop_zero (fun x => ‖f x‖)).eventually (gt_mem_nhds hε)).exists
  -- the coordinates of `S`
  set Sid : Finset (Ideal (𝓞 F)) := S.image (·.1) ∪ S.image (·.2.1) ∪ S.image (·.2.2.1) ∪
    S.image (·.2.2.2) with hSid
  have hfin : {P : EP 𝔪 | ∃ I ∈ Sid, I ≠ ⊥ ∧ I ≤ P.1}.Finite := by
    have h1 : {P : Ideal (𝓞 F) | ∃ I ∈ Sid, I ≠ ⊥ ∧ I ≤ P}.Finite := by
      have : {P : Ideal (𝓞 F) | ∃ I ∈ Sid, I ≠ ⊥ ∧ I ≤ P} ⊆
          ⋃ I ∈ Sid, {P : Ideal (𝓞 F) | Ideal.absNorm P ≤ Ideal.absNorm I} := by
        rintro P ⟨I, hI, hI0, hle⟩
        refine Set.mem_biUnion hI ?_
        exact Nat.le_of_dvd (Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]))
          (Ideal.absNorm_dvd_absNorm_of_le hle)
      exact (Set.Finite.biUnion Sid.finite_toSet fun I _ =>
        Ideal.finite_setOfPred_absNorm_le _).subset this
    exact h1.preimage (f := fun P : EP 𝔪 => P.1) Subtype.val_injective.injOn
  refine ⟨hfin.toFinset, fun T hT => ?_⟩
  set T' := T.map (Function.Embedding.subtype _) with hT'
  have hT'p : ∀ Q ∈ T', Q.IsPrime := by
    intro Q hQ
    obtain ⟨P, -, rfl⟩ := Finset.mem_map.1 hQ
    exact P.2.1
  -- inside `S`, only `one4` survives
  have hsurv : ∀ x ∈ S, x ∈ Cop T' → x ∈ Om 𝔪 → x = one4 := by
    intro x hxS hxc hxO
    have hcoord : ∀ I ∈ Sid, IsExterior 𝔪 I → (∀ Q ∈ T', ¬ I ≤ Q) → I = ⊤ := by
      intro I hI hIe hIc
      by_contra hIt
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal I hIt
      have hEP := isEP_of_le hM hIe hle
      have hmem : (⟨M, hEP⟩ : EP 𝔪) ∈ T := hT (by
        rw [Set.Finite.mem_toFinset]; exact ⟨I, hI, hIe.1, hle⟩)
      exact hIc M (Finset.mem_map.2 ⟨_, hmem, rfl⟩) hle
    have m1 : x.1 ∈ Sid := by
      simp only [hSid, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Finset.mem_image_of_mem _ hxS)))
    have m2 : x.2.1 ∈ Sid := by
      simp only [hSid, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr (Finset.mem_image_of_mem _ hxS)))
    have m3 : x.2.2.1 ∈ Sid := by
      simp only [hSid, Finset.mem_union]
      exact Or.inl (Or.inr (Finset.mem_image_of_mem _ hxS))
    have m4 : x.2.2.2 ∈ Sid := by
      simp only [hSid, Finset.mem_union]
      exact Or.inr (Finset.mem_image_of_mem _ hxS)
    have e1 := hcoord _ m1 hxO.1 fun Q hQ => (hxc Q hQ).1
    have e2 := hcoord _ m2 hxO.2.1 fun Q hQ => (hxc Q hQ).2.1
    have e3 := hcoord _ m3 hxO.2.2.1 fun Q hQ => (hxc Q hQ).2.2.1
    have e4 := hcoord _ m4 hxO.2.2.2 fun Q hQ => (hxc Q hQ).2.2.2
    obtain ⟨x1, x2, x3, x4⟩ := x
    simp only at e1 e2 e3 e4
    rw [e1, e2, e3, e4]; rfl
  have hite : Summable (fun x : Tup F => if x = one4 then (1 : ℂ) else 0) :=
    (hasSum_ite_eq one4 (1 : ℂ)).summable
  have hpt : ∀ x, ‖(Cop T').indicator f x - (if x = one4 then (1 : ℂ) else 0)‖ ≤
      ({x | x ∉ S} : Set (Tup F)).indicator (fun x => ‖f x‖) x := by
    intro x
    by_cases hx1 : x = one4
    · subst hx1
      rw [Set.indicator_of_mem (one4_mem_Cop T' hT'p), h.one, if_pos rfl, sub_self, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
    rw [if_neg hx1, sub_zero]
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_notMem (show x ∉ {x | x ∉ S} from fun h' => h' hxS)]
      by_cases hxc : x ∈ Cop T'
      · rw [Set.indicator_of_mem hxc]
        by_cases hxO : x ∈ Om 𝔪
        · exact absurd (hsurv x hxS hxc hxO) hx1
        · rw [h.zero x hxO, norm_zero]
      · rw [Set.indicator_of_notMem hxc, norm_zero]
    · rw [Set.indicator_of_mem (show x ∈ {x | x ∉ S} from hxS)]
      exact norm_indicator_le_norm_self _ _
  rw [← tsum_ite_eq (one4 : Tup F) (fun _ => (1 : ℂ)),
    ← ((summable_norm_indicator h _).of_norm).tsum_sub hite]
  have hsn : Summable (fun x => ‖(Cop T').indicator f x - (if x = one4 then (1 : ℂ) else 0)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (h.summ.indicator _)
  refine lt_of_le_of_lt (norm_tsum_le_tsum_norm hsn) ?_
  refine lt_of_le_of_lt (hsn.tsum_le_tsum hpt (h.summ.indicator _)) ?_
  rw [← tsum_subtype {x | x ∉ S} (fun x => ‖f x‖)]
  exact hS

/-- **The Euler product.** -/
theorem euler4 (h : EulerHyp 𝔪 f A) :
    HasProd (fun P : EP 𝔪 => ∑' e, A P.1 e) (∑' x, f x) ∧
      ((∀ P : EP 𝔪, ∑' e, A P.1 e ≠ 0) → ∑' x, f x ≠ 0) := by
  classical
  set X := ∑' x, f x
  set S : Finset (EP 𝔪) → ℂ :=
    fun T => ∑' x, (Cop (T.map (Function.Embedding.subtype _))).indicator f x with hSdef
  have hEq : ∀ T : Finset (EP 𝔪), X = (∏ P ∈ T, ∑' e, A P.1 e) * S T := by
    intro T
    have := sieve_eq h (T.map (Function.Embedding.subtype _)) (by
      intro Q hQ
      obtain ⟨P, -, rfl⟩ := Finset.mem_map.1 hQ
      exact P.2)
    rw [Finset.prod_map] at this
    exact this
  have hS1 : Tendsto S atTop (𝓝 1) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨T₀, hT₀⟩ := sieve_tail h hε
    exact ⟨T₀, fun T hT => by rw [dist_eq_norm]; exact hT₀ T hT⟩
  constructor
  · have hev : ∀ᶠ T in atTop, ∏ P ∈ T, ∑' e, A P.1 e = X / S T := by
      filter_upwards [hS1.eventually_ne one_ne_zero] with T hT
      rw [hEq T, mul_div_assoc, div_self hT, mul_one]
    show Tendsto _ (SummationFilter.unconditional _).filter _
    simp only [SummationFilter.unconditional_filter]
    have : Tendsto (fun T => X / S T) atTop (𝓝 (X / 1)) := tendsto_const_nhds.div hS1 one_ne_zero
    rw [div_one] at this
    exact this.congr' (hev.mono fun T hT => hT.symm)
  · intro hne hX
    obtain ⟨T, hT⟩ := (hS1.eventually_ne one_ne_zero).exists
    have := hEq T
    rw [hX] at this
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun P _ => hne P) hT this.symm

end sieve

end C3A

end ArtinPrimitiveRoots

end
end

section
section
/-!
# T12B: elementary Euler-product glue for `HeckeChar.LSeries`

* `T12B.norm_le_one`: `‖χ I‖ ≤ 1` (values on coprime ideals are roots of unity: class group and
  `(𝓞/𝔪)ˣ` are finite).
* `T12B.lseries_eq_tsum`: `L(s, χ) = ∑'_I χ(I) N(I)^{-s}` for `Re s > 1`.
* `T12B.sieve`: `(∑' g) · ∏_{P ∈ T} (1 − g P) = ∑'_{I coprime to T} g I` for completely
  multiplicative `g` (finite Euler sieve; no infinite product needed).
* `T12B.sieve_bound`: the sieved sum is close to `1` once `T` kills a large finite set.
-/

namespace ArtinPrimitiveRoots

open NumberField Filter Topology
open scoped nonZeroDivisors

namespace T12B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Summability of `∑_I N(I)^{-σ}` -/

theorem lseriesSummable_card {y : ℝ} (hy : 1 < y) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) y := by
  have hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue F)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ F).comp tendsto_natCast_atTop_atTop).congr
      fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ))
    (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim))
    (fun _ ↦ Nat.cast_nonneg _) zero_le_one (s := (y : ℂ)) (by simpa using hy)
  simpa using h

instance fiber_finite (n : ℕ) : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

/-- `∑_I N(I)^{-σ}` converges for `σ > 1`. -/
theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)) := by
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
  rw [← e.summable_iff]
  refine (summable_sigma_of_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).2
    ⟨fun n => Summable.of_finite, ?_⟩
  refine (lseriesSummable_card (F := F) hσ).norm.congr fun n => ?_
  have hfib : ∀ y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
      ((Ideal.absNorm (e ⟨n, y⟩) : ℕ) : ℝ) ^ (-σ) = (n : ℝ) ^ (-σ) := fun y => by
    simp [e, Equiv.sigmaFiberEquiv, y.2]
  simp only [Function.comp_apply, hfib, tsum_const, nsmul_eq_mul, LSeries.norm_term_eq,
    Complex.ofReal_re, Complex.norm_natCast]
  split_ifs with hn
  · subst hn
    rw [Nat.cast_zero, Real.zero_rpow (by linarith), mul_zero]
  · rw [Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

/-! ### Basic facts on Hecke characters -/

theorem toFun_top {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) : χ.toFun ⊤ = 1 := by
  have := χ.map_principal' 1 one_ne_zero (by simp)
  rwa [Ideal.span_singleton_one] at this

theorem toFun_bot {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) : χ.toFun ⊥ = 0 :=
  (χ.eq_zero_iff' ⊥).2 (Or.inl rfl)

theorem toFun_pow {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (I : Ideal (𝓞 F)) (n : ℕ) :
    χ.toFun (I ^ n) = χ.toFun I ^ n := by
  induction n with
  | zero => simp [Ideal.one_eq_top, toFun_top]
  | succ n ih => rw [pow_succ, χ.map_mul', ih, pow_succ]

/-- **(a)** A Hecke character of nonzero modulus takes values of norm `≤ 1`. -/
theorem norm_le_one {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar F 𝔪) (I : Ideal (𝓞 F)) :
    ‖χ.toFun I‖ ≤ 1 := by
  by_cases h0 : χ.toFun I = 0
  · simp [h0]
  have hI : I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤ := by
    have := (χ.eq_zero_iff' I).not.1 h0
    push Not at this
    exact this
  set h := Fintype.card (ClassGroup (𝓞 F)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have hI0 : I ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero hI.1
  have hIh0 : I ^ h ∈ (Ideal (𝓞 F))⁰ := pow_mem hI0 h
  have hprin : (I ^ h).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff hIh0]
    have : (⟨I ^ h, hIh0⟩ : (Ideal (𝓞 F))⁰) = ⟨I, hI0⟩ ^ h := rfl
    rw [this, map_pow, hh, pow_card_eq_one]
  set β := Submodule.IsPrincipal.generator (I ^ h)
  have hβ : Ideal.span {β} = I ^ h := Ideal.span_singleton_generator (I ^ h)
  have hβ0 : β ≠ 0 := by
    intro hb
    rw [hb, Ideal.span_singleton_eq_bot.2 rfl] at hβ
    exact hI.1 (pow_eq_zero_iff hpos.ne' |>.1 hβ.symm)
  have hcop : Ideal.span {β} ⊔ 𝔪 = ⊤ := by
    rw [hβ, sup_comm]
    exact Ideal.sup_pow_eq_top' (by rw [sup_comm]; exact hI.2)
  have hunit : IsUnit (Ideal.Quotient.mk 𝔪 β) := by
    have h1 : (1 : 𝓞 F) ∈ Ideal.span {β} ⊔ 𝔪 := by rw [hcop]; trivial
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk 𝔪 a) ?_
    rw [← map_mul, mul_comm, ← sub_eq_iff_eq_add.2 hyz.symm, map_sub, map_one,
      Ideal.Quotient.eq_zero_iff_mem.2 hz, sub_zero]
  have : Finite (𝓞 F ⧸ 𝔪) := Ideal.finiteQuotientOfFreeOfNeBot 𝔪 h𝔪
  have : Finite (𝓞 F ⧸ 𝔪)ˣ := Finite.of_injective _ Units.val_injective
  set k := Nat.card (𝓞 F ⧸ 𝔪)ˣ
  have hk : 0 < k := Nat.card_pos
  have hβk : Ideal.Quotient.mk 𝔪 (β ^ k) = Ideal.Quotient.mk 𝔪 1 := by
    rw [map_pow, map_one, ← hunit.unit_spec, ← Units.val_pow_eq_pow_val, pow_card_eq_one',
      Units.val_one]
  have hval := χ.map_principal' (β ^ k) (pow_ne_zero _ hβ0) (Ideal.Quotient.eq.1 hβk)
  rw [← Ideal.span_singleton_pow, hβ, ← pow_mul, toFun_pow] at hval
  exact (Complex.norm_eq_one_of_pow_eq_one hval (Nat.mul_ne_zero hpos.ne' hk.ne')).le

/-! ### The Dirichlet series as a sum over ideals -/

/-- `g_s(I) = χ(I) N(I)^{-s}`. -/
noncomputable def gs {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (s : ℂ) (I : Ideal (𝓞 F)) : ℂ :=
  χ.toFun I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)

theorem gs_mul {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (s : ℂ) (I J : Ideal (𝓞 F)) :
    gs χ s (I * J) = gs χ s I * gs χ s J := by
  simp only [gs, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, χ.map_mul']
  ring

theorem gs_bot {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (s : ℂ) : gs χ s ⊥ = 0 := by
  simp [gs, toFun_bot]

theorem gs_top {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (s : ℂ) : gs χ s ⊤ = 1 := by
  simp [gs, toFun_top]

theorem norm_gs_le {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (hχ : ∀ I, ‖χ.toFun I‖ ≤ 1)
    {s : ℂ} {σ : ℝ} (hσ : σ ≤ s.re) (I : Ideal (𝓞 F)) :
    ‖gs χ s I‖ ≤ ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ) := by
  by_cases hI : Ideal.absNorm I = 0
  · rw [Ideal.absNorm_eq_zero_iff.1 hI, gs_bot, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 : (1 : ℝ) ≤ (Ideal.absNorm I : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hI
  rw [gs, norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hI), Complex.neg_re]
  calc ‖χ.toFun I‖ * (Ideal.absNorm I : ℝ) ^ (-s.re)
      ≤ 1 * (Ideal.absNorm I : ℝ) ^ (-σ) :=
        mul_le_mul (hχ I) (Real.rpow_le_rpow_of_exponent_le h1 (by linarith))
          (Real.rpow_nonneg (by positivity) _) zero_le_one
    _ = _ := one_mul _

theorem summable_gs {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (hχ : ∀ I, ‖χ.toFun I‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) : Summable (gs χ s) :=
  Summable.of_norm_bounded (summable_absNorm_rpow hs) (norm_gs_le χ hχ le_rfl)

/-- `L(s, χ) = ∑'_I χ(I) N(I)^{-s}` on `Re s > 1`. -/
theorem lseries_eq_tsum {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (hχ : ∀ I, ‖χ.toFun I‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) : χ.LSeries s = ∑' I, gs χ s I := by
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
  have hsum := summable_gs χ hχ hs
  have hs2 : Summable (fun p => gs χ s (e p)) := (Equiv.summable_iff (f := gs χ s) e).2 hsum
  rw [← e.tsum_eq, hs2.tsum_sigma, HeckeChar.LSeries, LSeries]
  congr 1
  funext n
  have hfib : ∀ y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
      gs χ s (e ⟨n, y⟩) = χ.toFun y.1 * (n : ℂ) ^ (-s) := fun y => by
    simp [e, Equiv.sigmaFiberEquiv, gs, y.2]
  simp only [hfib]
  rw [tsum_mul_right]
  have hcoeff : (∑' y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}, χ.toFun y.1) = χ.coeff n := by
    rw [HeckeChar.coeff, finsum_mem_def,
      ← tsum_eq_finsum (L := SummationFilter.unconditional (Ideal (𝓞 F)))
        ((Ideal.finite_setOfPred_absNorm_eq n).subset
        Set.support_indicator_subset),
      ← tsum_subtype]
    rfl
  rw [hcoeff]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, Nat.cast_zero, Complex.zero_cpow, mul_zero]
    intro h
    have : s = 0 := neg_eq_zero.1 h
    rw [this, Complex.zero_re] at hs
    linarith
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]

/-! ### The finite sieve -/

end T12B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3A_Euler1: Euler products of `L(s, χ)` and `ζ^S(s)` over the exterior primes

From `euler4` (one active coordinate) and T12B's sieve:
* `hasProd_inv_LSeries`: `∏_{P ∉ S} (1 − χ(P) N P^{-s}) = L(s, χ)⁻¹` for `Re s > 1`;
* `hasProd_zetaS`: `∏_{P ∉ S} (1 − N P^{-s})⁻¹ = ∏_{P ⊇ 𝔪} (1 − N P^{-s}) · ζ_F(s)`. -/

open NumberField Filter Topology

namespace ArtinPrimitiveRoots

namespace C3A

variable {F : Type*} [Field F] [NumberField F]

lemma sup_mul_eq_top_iff {𝔪 I J : Ideal (𝓞 F)} :
    I * J ⊔ 𝔪 = ⊤ ↔ I ⊔ 𝔪 = ⊤ ∧ J ⊔ 𝔪 = ⊤ := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [eq_top_iff, ← h]; exact sup_le_sup_right Ideal.mul_le_left _
    · rw [eq_top_iff, ← h]; exact sup_le_sup_right Ideal.mul_le_right _
  · rintro ⟨h1, h2⟩
    rw [Ideal.mul_sup_eq_of_coprime_left h1, h2]

/-! ### The one-variable Euler product from `euler4` -/

section one

variable {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (s : ℂ)

/-- The function `χ(I) N I^{-s}` placed on the first coordinate. -/
noncomputable def f1 (x : Tup F) : ℂ := by
  classical exact if x.2 = (⊤, ⊤, ⊤) then T12B.gs χ s x.1 else 0

/-- Its local factors. -/
noncomputable def A1 (P : Ideal (𝓞 F)) (e : Exps) : ℂ := by
  classical exact if e.2 = (0, 0, 0) then T12B.gs χ s P ^ e.1 else 0

lemma pow_mul_eq_top {P I : Ideal (𝓞 F)} (hP : P.IsPrime) {k : ℕ} :
    P ^ k * I = ⊤ ↔ k = 0 ∧ I = ⊤ := by
  constructor
  · intro h
    rcases k with _ | k
    · simp only [pow_zero, one_mul] at h; exact ⟨rfl, h⟩
    · exfalso; apply hP.ne_top
      rw [eq_top_iff, ← h, pow_succ', mul_assoc]; exact Ideal.mul_le_left
  · rintro ⟨rfl, rfl⟩; simp

theorem euler1 (hχ : ∀ I, ‖χ.toFun I‖ ≤ 1) (hs : 1 < s.re) :
    HasProd (fun P : EP 𝔪 => (1 - χ.toFun P.1 * ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹)
      (χ.LSeries s) ∧ χ.LSeries s ≠ 0 := by
  classical
  have hg : ∀ P : Ideal (𝓞 F), IsEP 𝔪 P → ‖T12B.gs χ s P‖ < 1 := by
    intro P hP
    have h2 := two_le_absNorm hP.1 hP.2.1
    refine lt_of_le_of_lt (T12B.norm_gs_le χ hχ (le_refl s.re) P) ?_
    have hq : (1 : ℝ) < ((Ideal.absNorm P : ℕ) : ℝ) := by exact_mod_cast h2
    exact Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  have hinj : Function.Injective (fun c : Ideal (𝓞 F) => ((c, ⊤, ⊤, ⊤) : Tup F)) := by
    intro a b h; simpa using h
  have hsupp : Function.support (f1 χ s) ⊆ Set.range (fun c : Ideal (𝓞 F) => ((c, ⊤, ⊤, ⊤) : Tup F)) := by
    intro x hx
    simp only [Function.mem_support, f1] at hx
    split_ifs at hx with h
    swap
    · exact absurd rfl hx
    obtain ⟨x1, x2⟩ := x
    simp only at h
    exact ⟨x1, by rw [h]⟩
  have hcomp : (f1 χ s) ∘ (fun c : Ideal (𝓞 F) => ((c, ⊤, ⊤, ⊤) : Tup F)) = T12B.gs χ s := by
    funext c; simp [f1]
  have hsumm : Summable (T12B.gs χ s) := T12B.summable_gs χ hχ hs
  have hH : EulerHyp 𝔪 (f1 χ s) (A1 χ s) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      simp only [f1]
      split_ifs with h
      · obtain ⟨x1, x2⟩ := x
        simp only at h
        subst h
        have : ¬ IsExterior 𝔪 x1 := fun h' => hx ⟨h', ⟨top_ne_bot, top_sup_eq _⟩,
          ⟨top_ne_bot, top_sup_eq _⟩, ⟨top_ne_bot, top_sup_eq _⟩⟩
        simp only [T12B.gs]
        rw [(χ.eq_zero_iff' x1).2 (by
          by_contra hc; push Not at hc; exact this hc), zero_mul]
      · rfl
    · simp [f1, one4, T12B.gs_top]
    · intro P hP e y hyO hyP
      obtain ⟨e1, e2, e3, e4⟩ := e
      obtain ⟨y1, y2, y3, y4⟩ := y
      simp only [f1, A1, pw, Prod.mk.injEq]
      by_cases he : e2 = 0 ∧ e3 = 0 ∧ e4 = 0
      · obtain ⟨rfl, rfl, rfl⟩ := he
        simp only [pow_zero, one_mul, and_self, if_true]
        split_ifs
        · have hpow : T12B.gs χ s (P ^ e1) = T12B.gs χ s P ^ e1 := by
            induction e1 with
            | zero => simp [T12B.gs_top]
            | succ k ih => rw [pow_succ, T12B.gs_mul, ih, pow_succ]
          rw [T12B.gs_mul, hpow]
        · rw [mul_zero]
      · rw [if_neg, if_neg he, zero_mul]
        rintro ⟨h2, h3, h4⟩
        rw [pow_mul_eq_top hP.1] at h2 h3 h4
        exact he ⟨h2.1, h3.1, h4.1⟩
    · rw [← hinj.summable_iff (fun x hx => by
        by_contra h; exact hx (hsupp (norm_ne_zero_iff.1 h)))]
      rw [show (fun x => ‖f1 χ s x‖) ∘ (fun c : Ideal (𝓞 F) => ((c, ⊤, ⊤, ⊤) : Tup F)) =
        fun c => ‖T12B.gs χ s c‖ by rw [← hcomp]; rfl]
      exact Summable.of_norm_bounded (T12B.summable_absNorm_rpow hs)
        (fun c => by rw [norm_norm]; exact T12B.norm_gs_le χ hχ le_rfl c)
    · intro P hP
      have hgeo := summable_geometric_of_lt_one (norm_nonneg _) (hg P hP)
      have hinj' : Function.Injective (fun k : ℕ => ((k, 0, 0, 0) : Exps)) := by
        intro a b h; simpa using h
      rw [← hinj'.summable_iff (fun e he => by
        obtain ⟨e1, e2⟩ := e
        simp only [A1]
        rw [if_neg, norm_zero]
        intro h; exact he ⟨e1, by rw [h]⟩)]
      refine hgeo.congr fun k => ?_
      simp [A1]
  obtain ⟨hprod, hne⟩ := euler4 hH
  have htsum : ∑' x, f1 χ s x = χ.LSeries s := by
    rw [← hinj.tsum_eq hsupp]
    show ∑' c, ((f1 χ s) ∘ (fun c : Ideal (𝓞 F) => ((c, ⊤, ⊤, ⊤) : Tup F))) c = _
    rw [hcomp, T12B.lseries_eq_tsum χ hχ hs]
  have hloc : ∀ P : EP 𝔪, ∑' e, A1 χ s P.1 e =
      (1 - χ.toFun P.1 * ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹ := by
    intro P
    have hinj' : Function.Injective (fun k : ℕ => ((k, 0, 0, 0) : Exps)) := by
      intro a b h; simpa using h
    rw [← hinj'.tsum_eq (fun e he => by
      obtain ⟨e1, e2⟩ := e
      simp only [Function.mem_support, A1] at he
      split_ifs at he with h'
      · exact ⟨e1, by rw [h']⟩
      · exact absurd rfl he)]
    simp only [A1, if_true]
    exact tsum_geometric_of_norm_lt_one (hg P.1 P.2)
  rw [htsum] at hprod hne
  refine ⟨?_, ?_⟩
  · exact hprod.congr_fun fun P => (hloc P).symm
  · refine hne fun P => ?_
    rw [hloc P]
    refine inv_ne_zero fun h => ?_
    have := hg P.1 P.2
    rw [sub_eq_zero] at h
    have h' : T12B.gs χ s P.1 = 1 := h.symm
    rw [h', norm_one] at this
    exact lt_irrefl _ this

end one

/-! ### `ζ^S` -/

lemma finite_primes_ge {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) :
    {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P}.Finite := by
  refine (Ideal.finite_setOfPred_absNorm_le (Ideal.absNorm 𝔪)).subset ?_
  intro P ⟨_, _, hle'⟩
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]))
    (Ideal.absNorm_dvd_absNorm_of_le hle')

end C3A

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3K_Hecke: an abelian Artin character as a `HeckeChar` of modulus its conductor

For `K` totally complex, `M/K` Galois and `ψ : Gal(M/K) →* ℂˣ`, library 41aa80ff gives a narrow ray
class character `χ_R` mod `𝔣 = conductor ψ` with `χ_R(v) = localValue ψ v`. Then
`psiH I = χ_R([I])` (on `I` coprime to `𝔣`) is a `HeckeChar K 𝔣` with `psiH = idealValue ψ` on nonzero
ideals, so `ArtinL.Abelian.LSeries ψ = psiH.LSeries`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ)

/-- The ray class character of 41aa80ff. -/
def chiR : NarrowRayClassGroup K (ArtinL.Abelian.conductor ψ) →* ℂ :=
  (ArtinL.Abelian.exists_narrowRayClassChar_conductor_eq_localValue_u0 K M ψ).choose

open scoped Classical in
lemma chiR_spec :
    (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ ArtinL.Abelian.conductor ψ),
        chiR ψ (primeClass K (ArtinL.Abelian.conductor ψ) v hv) = ArtinL.Abelian.localValue ψ v) ∧
      (chiR ψ = 1 ↔ ψ = 1) ∧
      (∀ (α : 𝓞 K) (hα : α ≠ 0)
        (hc : principalUnit K α hα ∈ coprimeToModulus K (ArtinL.Abelian.conductor ψ)),
        α - 1 ∈ ArtinL.Abelian.conductor ψ →
          chiR ψ (NarrowRayClassGroup.mk K (ArtinL.Abelian.conductor ψ) ⟨principalUnit K α hα, hc⟩) =
            ∏ w ∈ (Finset.univ.filter fun w : {w : InfinitePlace K // w.IsReal} =>
                ¬ ArtinL.Abelian.IsPlusAt ψ w.1),
              ((SignType.sign (embedding_of_isReal w.2 (α : K)) : ℤ) : ℂ)) := by
  have h := (ArtinL.Abelian.exists_narrowRayClassChar_conductor_eq_localValue_u0 K M ψ).choose_spec
  exact ⟨h.1, h.2.1, h.2.2.1⟩

lemma chiR_ne_zero (C : NarrowRayClassGroup K (ArtinL.Abelian.conductor ψ)) : chiR ψ C ≠ 0 := by
  intro h
  have : chiR ψ C * chiR ψ C⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [h, zero_mul] at this; exact zero_ne_one this

lemma sup_eq_top_iff_not_dvd (v : HeightOneSpectrum (𝓞 K)) (𝔣 : Ideal (𝓞 K)) :
    v.asIdeal ⊔ 𝔣 = ⊤ ↔ ¬ v.asIdeal ∣ 𝔣 := by
  rw [Ideal.dvd_iff_le]
  constructor
  · intro h hle
    apply v.isPrime.ne_top; rw [← h]; exact le_antisymm le_sup_left (sup_le le_rfl hle)
  · intro h
    by_contra hne
    have e := v.isMaximal.eq_of_le hne le_sup_left
    exact h (e ▸ le_sup_right)

open Classical in
lemma cls_mul {𝔣 : Ideal (𝓞 K)} {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥ ∧ I ⊔ 𝔣 = ⊤)
    (hJ : J ≠ ⊥ ∧ J ⊔ 𝔣 = ⊤) (hIJ : I * J ≠ ⊥ ∧ I * J ⊔ 𝔣 = ⊤) :
    T12A.cls 𝔣 (I * J) = T12A.cls 𝔣 I * T12A.cls 𝔣 J := by
  rw [T12A.cls, T12A.cls, T12A.cls, dif_pos hI, dif_pos hJ, dif_pos hIJ, ← map_mul]
  congr 1
  apply Subtype.ext
  show FractionalIdeal.mk0 K ⟨I * J, _⟩ = FractionalIdeal.mk0 K ⟨I, _⟩ * FractionalIdeal.mk0 K ⟨J, _⟩
  rw [← map_mul]; rfl

open Classical in
/-- The Hecke character `psiH` of modulus `conductor ψ`. -/
def psiH (hK : ∀ w : InfinitePlace K, w.IsComplex) :
    HeckeChar K (ArtinL.Abelian.conductor ψ) where
  toFun I := if I ≠ ⊥ ∧ I ⊔ ArtinL.Abelian.conductor ψ = ⊤ then
    chiR ψ (T12A.cls (ArtinL.Abelian.conductor ψ) I) else 0
  map_mul' I J := by
    have hb : I * J ≠ ⊥ ↔ I ≠ ⊥ ∧ J ≠ ⊥ := by
      simp only [ne_eq, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
    by_cases hI : I ≠ ⊥ ∧ I ⊔ ArtinL.Abelian.conductor ψ = ⊤ <;>
      by_cases hJ : J ≠ ⊥ ∧ J ⊔ ArtinL.Abelian.conductor ψ = ⊤
    · have hIJ : I * J ≠ ⊥ ∧ I * J ⊔ ArtinL.Abelian.conductor ψ = ⊤ :=
        ⟨hb.2 ⟨hI.1, hJ.1⟩, C3A.sup_mul_eq_top_iff.2 ⟨hI.2, hJ.2⟩⟩
      rw [if_pos hIJ, if_pos hI, if_pos hJ, cls_mul hI hJ hIJ, map_mul]
    · rw [if_neg hJ, mul_zero, if_neg]
      rintro ⟨h1, h2⟩; exact hJ ⟨(hb.1 h1).2, (C3A.sup_mul_eq_top_iff.1 h2).2⟩
    · rw [if_neg hI, zero_mul, if_neg]
      rintro ⟨h1, h2⟩; exact hI ⟨(hb.1 h1).1, (C3A.sup_mul_eq_top_iff.1 h2).1⟩
    · rw [if_neg hI, zero_mul, if_neg]
      rintro ⟨h1, h2⟩; exact hI ⟨(hb.1 h1).1, (C3A.sup_mul_eq_top_iff.1 h2).1⟩
  eq_zero_iff' I := by
    split_ifs with h
    · simp only [chiR_ne_zero, false_iff, not_or, not_not]; exact h
    · simp only [true_iff]; by_contra h'; push Not at h'; exact h h'
  map_principal' α hα h1 := by
    have hc : Ideal.span {α} ≠ ⊥ ∧ Ideal.span {α} ⊔ ArtinL.Abelian.conductor ψ = ⊤ :=
      ⟨T12A.span_ne_bot hα, T12A.span_sup_eq_top h1⟩
    rw [if_pos hc, T12A.cls, dif_pos hc]
    have hpc : principalUnit K α hα ∈ coprimeToModulus K (ArtinL.Abelian.conductor ψ) :=
      (T12A.mk0_mem_coprimeToModulus_iff _).2 hc.2
    have := (chiR_spec ψ).2.2 α hα hpc h1
    refine (congrArg (chiR ψ) (congrArg (NarrowRayClassGroup.mk K (ArtinL.Abelian.conductor ψ))
      (Subtype.ext rfl))).trans (this.trans ?_)
    apply Finset.prod_eq_one
    intro w _
    exact absurd w.2 (not_isReal_iff_isComplex.2 (hK w.1))

variable (hK : ∀ w : InfinitePlace K, w.IsComplex)

lemma psiH_prime (v : HeightOneSpectrum (𝓞 K)) :
    (psiH ψ hK).toFun v.asIdeal = ArtinL.Abelian.localValue ψ v := by
  classical
  by_cases hv : v.asIdeal ∣ ArtinL.Abelian.conductor ψ
  · have h1 : ¬ (v.asIdeal ≠ ⊥ ∧ v.asIdeal ⊔ ArtinL.Abelian.conductor ψ = ⊤) := fun h =>
      (sup_eq_top_iff_not_dvd v _).1 h.2 hv
    have h2 := (ArtinL.Abelian.dvd_conductor_iff_not_isUnramifiedAt K M ψ v).1 hv
    show (if _ then _ else _) = _
    rw [if_neg h1, ArtinL.Abelian.localValue, if_neg h2]
  · have h1 : v.asIdeal ≠ ⊥ ∧ v.asIdeal ⊔ ArtinL.Abelian.conductor ψ = ⊤ :=
      ⟨v.ne_bot, (sup_eq_top_iff_not_dvd v _).2 hv⟩
    show (if _ then _ else _) = _
    rw [if_pos h1, T12A.cls, dif_pos h1, ← (chiR_spec ψ).1 v hv]
    rfl

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_Conv: the convexity bound for an abelian Artin `L`-function with explicit conductor

For `K` totally complex, `ψ ≠ 1`: the entire continuation `L` of `L(s, ψ)` satisfies
`‖L(s)‖ ≤ C (N 𝔣_ψ)^{1/2+δ} (1 + |t|)^{3 r₂}` on `−δ ≤ Re s ≤ 4`, with `C` depending only on `K`
and `δ`, provided `L` has some polynomial growth on the strip (`GrowthHyp`, from L3K_Growth).

Inputs: the FE 3508ac81 (`Λ(1−s) = W Λ'(s)`), `|W| = 1` from `Λ' = conj ∘ Λ ∘ conj`, the Gamma
ratio of L3K_Gamma, and Phragmén–Lindelöf 40726dc6. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace IsDedekindDomain Complex

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

/-- Identity theorem for entire functions agreeing on `Re s > 1`. -/
lemma entire_ext {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ s : ℂ, 1 < s.re → f s = g s) : f = g := by
  have hfa : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hga : AnalyticOnNhd ℂ g Set.univ := hg.differentiableOn.analyticOnNhd isOpen_univ
  refine AnalyticOnNhd.eq_of_eventuallyEq hfa hga (z₀ := 2) ?_
  have ho : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [ho.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with s hs using h s hs

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ)

lemma nrRealPlaces_eq_zero (hK : ∀ w : InfinitePlace K, w.IsComplex) : nrRealPlaces K = 0 := by
  haveI : IsTotallyComplex K := ⟨hK⟩
  exact IsTotallyComplex.nrRealPlaces_eq_zero K

lemma natCast_cpow_conj (n : ℕ) (s : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ (starRingEnd ℂ) s) = (n : ℂ) ^ s := by
  rw [Complex.cpow_conj _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm),
    Complex.conj_natCast, RCLike.conj_conj]

lemma ofReal_cpow_conj {x : ℝ} (hx : 0 ≤ x) (s : ℂ) :
    (starRingEnd ℂ) ((x : ℂ) ^ (starRingEnd ℂ) s) = (x : ℂ) ^ s := by
  rw [Complex.cpow_conj _ _ (by rw [Complex.arg_ofReal_of_nonneg hx]; exact Real.pi_ne_zero.symm),
    Complex.conj_ofReal, RCLike.conj_conj]

lemma Gammaℂ_conj (s : ℂ) : Gammaℂ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Gammaℂ s) := by
  have h := ofReal_cpow_conj (x := 2 * Real.pi) (by positivity) ((starRingEnd ℂ) (-s))
  rw [RCLike.conj_conj] at h
  push_cast at h
  rw [map_neg] at h
  rw [Gammaℂ_def, Gammaℂ_def, map_mul, map_mul, Gamma_conj, h, map_ofNat]

/-- `Z(σ) = ∑_I N(I)^{-σ}`. -/
def Zsum (K : Type) [Field K] [NumberField K] (σ : ℝ) : ℝ :=
  ∑' I : Ideal (𝓞 K), ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)

lemma Zsum_nonneg (σ : ℝ) : 0 ≤ Zsum K σ :=
  tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma poly_le_exp_exp {A : ℝ} (hA : 0 ≤ A) (N : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    A * (1 + x) ^ N ≤ Real.exp ((A + N) * Real.exp x) := by
  have h1 : (1 + x) ^ N ≤ Real.exp (N * x) := by
    rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) N
  have h2 : A ≤ Real.exp A := by linarith [Real.add_one_le_exp A]
  have hex : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hex1 : 1 ≤ Real.exp x := Real.one_le_exp hx
  calc A * (1 + x) ^ N ≤ Real.exp A * Real.exp (N * x) :=
        mul_le_mul h2 h1 (by positivity) (by positivity)
    _ = Real.exp (A + N * x) := by rw [Real.exp_add]
    _ ≤ Real.exp ((A + N) * Real.exp x) := by
        apply Real.exp_le_exp.2
        have : (N : ℝ) * x ≤ N * Real.exp x := mul_le_mul_of_nonneg_left hex (Nat.cast_nonneg _)
        nlinarith

/-- `‖Γ_ℂ(1 − z)/Γ_ℂ(z)‖ ≤ 4 e^π Γ(1+δ)² (1 + |t|)³` on `Re z = −δ`. -/
lemma norm_Gammaℂ_ratio_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {z : ℂ} (hz : z.re = -δ) :
    ‖Gammaℂ (1 - z) / Gammaℂ z‖ ≤
      4 * Real.exp Real.pi * Real.Gamma (1 + δ) ^ 2 * (1 + |z.im|) ^ 3 := by
  have hz' : z = (-δ : ℂ) + z.im * I := by
    apply Complex.ext <;> simp [hz]
  have h1z : 1 - z = 1 + δ - z.im * I := by apply Complex.ext <;> simp [hz]
  have hΓ := L3K.norm_Gamma_ratio_le hδ0 hδ1 z.im
  rw [← h1z, ← hz'] at hΓ
  have h2π : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hne : Gamma z ≠ 0 := by
    intro h0
    rw [h0, div_zero, norm_zero] at hΓ
    exact absurd h0 (Gamma_ne_zero fun m hm => by
      have := congrArg Complex.re hm; simp at this; rw [hz] at this
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp at this; linarith
      · have : (1 : ℝ) ≤ m := by exact_mod_cast h
        linarith)
  rw [Gammaℂ_def, Gammaℂ_def, h2π]
  have e : 2 * ((2 * Real.pi : ℝ) : ℂ) ^ (-(1 - z)) * Gamma (1 - z) /
      (2 * ((2 * Real.pi : ℝ) : ℂ) ^ (-z) * Gamma z) =
      (((2 * Real.pi : ℝ) : ℂ) ^ (-(1 - z)) / ((2 * Real.pi : ℝ) : ℂ) ^ (-z)) *
        (Gamma (1 - z) / Gamma z) := by
    have : ((2 * Real.pi : ℝ) : ℂ) ^ (-z) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h; exact absurd h (by exact_mod_cast hpos.ne')
    field_simp
  rw [e, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hpos,
    Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have hre1 : (-(1 - z)).re = -(1 + δ) := by simp [hz]; ring
  have hre2 : (-z).re = δ := by simp [hz]
  rw [hre1, hre2]
  have hq : (2 * Real.pi) ^ (-(1 + δ)) / (2 * Real.pi) ^ δ ≤ 1 := by
    rw [div_le_one (Real.rpow_pos_of_pos hpos _)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
  calc (2 * Real.pi) ^ (-(1 + δ)) / (2 * Real.pi) ^ δ * ‖Gamma (1 - z) / Gamma z‖
      ≤ 1 * ‖Gamma (1 - z) / Gamma z‖ := mul_le_mul_of_nonneg_right hq (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hΓ

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_Growth: the a-priori growth hypothesis for Phragmén–Lindelöf

For `ψ ≠ 1`, the entire continuation of `L(s, ψ)` has polynomial growth on every vertical strip:
library c46e3955 applied to the idelic character `η` of f982cbad attached to `χ_R` (41aa80ff), with
`T` the primes dividing the conductor, and the Euler product of `psiH` (C3A `euler1`).
`η` is nontrivial on the norm-one ideles: otherwise `η = |·|^{it}` (a55d6ac4), finite order forces
`t = 0` (86a18a2c), and then `χ_R = 1` because the prime classes generate the ray class group. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply nonZeroDivisors
  AutomorphicForm NumberField.TateGlobal NumberField.AdelicLevel

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

section Gen

variable {K : Type} [Field K] [NumberField K]

/-- The prime classes generate the narrow ray class group. -/
theorem eq_one_of_primeClass {𝔣 : Ideal (𝓞 K)} (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (h : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣), χ (primeClass K 𝔣 v hv) = 1) :
    χ = 1 := by
  classical
  set χu : NarrowRayClassGroup K 𝔣 →* ℂˣ := χ.toHomUnits
  set Kr : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
    ((χu.comp (NarrowRayClassGroup.mk K 𝔣)).ker).map (coprimeToModulus K 𝔣).subtype
  have hP : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 → primeUnit K v ∈ Kr := by
    intro v hv
    refine ⟨⟨primeUnit K v, primeUnit_mem_coprimeToModulus K hv⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply]
    apply Units.ext
    rw [MonoidHom.coe_toHomUnits, Units.val_one]
    exact h v hv
  have hall : ∀ y : ↥(coprimeToModulus K 𝔣), (y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ Kr := by
    intro y
    set I : FractionalIdeal (𝓞 K)⁰ K := ((y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
    have hI : I ≠ 0 := Units.ne_zero _
    have hfin := FractionalIdeal.finite_factors (K := K) I
    rw [Filter.eventually_cofinite] at hfin
    set S := hfin.toFinset
    have hy : (y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ∏ v ∈ S, primeUnit K v ^ FractionalIdeal.count K v I := by
      apply Units.ext
      rw [Units.coe_prod]
      conv_lhs => rw [show ((y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = I from rfl,
        ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI]
      rw [finprod_eq_prod_of_mulSupport_subset]
      · refine Finset.prod_congr rfl fun v _ => ?_
        rw [Units.val_zpow_eq_zpow_val, primeUnit_val]
      · intro v hv
        rw [Set.Finite.coe_toFinset]
        intro h0
        apply hv
        simp only at h0 ⊢
        rw [h0, zpow_zero]
    rw [hy]
    refine Subgroup.prod_mem _ fun v hv => ?_
    by_cases hd : v.asIdeal ∣ 𝔣
    · have : FractionalIdeal.count K v I = 0 := ((mem_coprimeToModulus_iff K).1 y.2) v hd
      rw [this, zpow_zero]; exact Subgroup.one_mem _
    · exact Subgroup.zpow_mem _ (hP v hd) _
  refine MonoidHom.ext fun C => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective C
  obtain ⟨z, hz, hzy⟩ := hall y
  have hzy' : z = y := Subtype.ext hzy
  rw [hzy'] at hz
  rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply] at hz
  have := congrArg (fun x : ℂˣ => (x : ℂ)) hz
  simp only [MonoidHom.coe_toHomUnits, Units.val_one] at this
  rw [MonoidHom.one_apply]
  exact this

/-- An idelic character admitting `𝔣` as a modulus is unramified at `v ∤ 𝔣`. -/
theorem isUnramifiedCharAt_of_admitsModulus {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    {η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hη : HeckeCharacter.AdmitsModulus K η 𝔣)
    {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣) : IsUnramifiedCharAt η v := by
  classical
  intro t ht hti
  unfold localChar
  apply hη
  · rfl
  · intro w
    by_cases hw : w = v
    · subst hw
      have hval : Valued.v ((t : w.adicCompletion K)) = 1 := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ht hti
        apply le_antisymm ht
        have h1 : Valued.v ((t : w.adicCompletion K)) * Valued.v (((t⁻¹ : (w.adicCompletion K)ˣ) :
            w.adicCompletion K)) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        by_contra hlt
        push Not at hlt
        have : Valued.v ((t : w.adicCompletion K)) * Valued.v (((t⁻¹ : (w.adicCompletion K)ˣ) :
            w.adicCompletion K)) < 1 :=
          mul_lt_one_of_lt_of_le hlt hti
        rw [h1] at this; exact lt_irrefl _ this
      have hm : HeckeCharacter.idealMultiplicity K w 𝔣 = 0 := by
        unfold HeckeCharacter.idealMultiplicity
        by_contra h0
        exact hv ((Associates.count_ne_zero_iff_dvd h𝔣 w.irreducible).1 h0)
      show Valued.v (((localUnit (𝓞 K) K w t : (FiniteAdeleRing (𝓞 K) K)ˣ) :
          FiniteAdeleRing (𝓞 K) K) w) = 1 ∧ Valued.v (((localUnit (𝓞 K) K w t :
          (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w - 1) ≤ _
      rw [localUnit_apply_self, hm, Nat.cast_zero, neg_zero, WithZero.exp_zero]
      refine ⟨hval, ?_⟩
      refine (Valuation.map_sub _ _ _).trans (max_le hval.le (by rw [map_one]))
    · show Valued.v (((localUnit (𝓞 K) K v t : (FiniteAdeleRing (𝓞 K) K)ˣ) :
          FiniteAdeleRing (𝓞 K) K) w) = 1 ∧ Valued.v (((localUnit (𝓞 K) K v t :
          (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w - 1) ≤ _
      rw [localUnit_apply_of_ne _ _ _ _ hw, map_one, sub_self, map_zero]
      exact ⟨rfl, zero_le⟩

end Gen

section Main

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ)

end Main

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3W_Ray: change of modulus and primitive reduction for narrow ray class characters

`K` totally complex. For `𝔣₁ ≤ 𝔣₂` (`𝔣₂ ∣ 𝔣₁`) the natural map `π : Cl⁺_{𝔣₁} → Cl⁺_{𝔣₂}` is onto and
its kernel is generated by classes `(α)`, `α ≡ 1 (mod 𝔣₂)`, `α` prime to `𝔣₁`. Hence a character
trivial on those classes descends (`descend`), and every character has a primitive model
(`exists_primitive`). -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3W

variable {K : Type} [Field K] [NumberField K]

lemma no_real (hK : ∀ w : InfinitePlace K, w.IsComplex) (τ : K →+* ℝ) : False := by
  set φ : K →+* ℂ := Complex.ofRealHom.comp τ
  have hw : (InfinitePlace.mk φ).IsReal := by
    rw [InfinitePlace.isReal_mk_iff, NumberField.ComplexEmbedding.isReal_iff]
    ext x; simp [φ, NumberField.ComplexEmbedding.conjugate_coe_eq]
  exact (not_isReal_iff_isComplex.2 (hK _)) hw

/-- A subgroup of `Cl⁺_𝔣` containing every prime class is everything. -/
theorem mem_of_primeClass {𝔣 : Ideal (𝓞 K)} (H : Subgroup (NarrowRayClassGroup K 𝔣))
    (h : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣), primeClass K 𝔣 v hv ∈ H)
    (C : NarrowRayClassGroup K 𝔣) : C ∈ H := by
  classical
  set Kr : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
    (H.comap (NarrowRayClassGroup.mk K 𝔣)).map (coprimeToModulus K 𝔣).subtype
  have hP : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 → primeUnit K v ∈ Kr := fun v hv =>
    ⟨⟨primeUnit K v, primeUnit_mem_coprimeToModulus K hv⟩, h v hv, rfl⟩
  have hall : ∀ y : ↥(coprimeToModulus K 𝔣), (y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ Kr := by
    intro y
    set I : FractionalIdeal (𝓞 K)⁰ K := ((y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
    have hI : I ≠ 0 := Units.ne_zero _
    have hfin := FractionalIdeal.finite_factors (K := K) I
    rw [Filter.eventually_cofinite] at hfin
    have hy : (y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
        ∏ v ∈ hfin.toFinset, primeUnit K v ^ FractionalIdeal.count K v I := by
      apply Units.ext
      rw [Units.coe_prod]
      conv_lhs => rw [show ((y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = I from rfl,
        ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI]
      rw [finprod_eq_prod_of_mulSupport_subset]
      · refine Finset.prod_congr rfl fun v _ => ?_
        rw [Units.val_zpow_eq_zpow_val, primeUnit_val]
      · intro v hv
        rw [Set.Finite.coe_toFinset]
        intro h0
        apply hv
        simp only at h0 ⊢
        rw [h0, zpow_zero]
    rw [hy]
    refine Subgroup.prod_mem _ fun v _ => ?_
    by_cases hd : v.asIdeal ∣ 𝔣
    · have : FractionalIdeal.count K v I = 0 := ((mem_coprimeToModulus_iff K).1 y.2) v hd
      rw [this, zpow_zero]; exact Subgroup.one_mem _
    · exact Subgroup.zpow_mem _ (hP v hd) _
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective C
  obtain ⟨z, hz, hzy⟩ := hall y
  have hzy' : z = y := Subtype.ext hzy
  rw [hzy'] at hz
  exact hz

lemma coprime_mono {𝔣₁ 𝔣₂ : Ideal (𝓞 K)} (h : 𝔣₁ ≤ 𝔣₂) :
    coprimeToModulus K 𝔣₁ ≤ coprimeToModulus K 𝔣₂ := by
  intro y hy
  rw [mem_coprimeToModulus_iff] at hy ⊢
  intro v hv
  exact hy v (dvd_trans hv (Ideal.dvd_iff_le.2 h))

lemma narrow_mono {𝔣₁ 𝔣₂ : Ideal (𝓞 K)} (h : 𝔣₁ ≤ 𝔣₂) :
    narrowRaySubgroup K 𝔣₁ ≤ narrowRaySubgroup K 𝔣₂ := by
  apply Subgroup.closure_mono
  rintro I ⟨α, h0, h1, hpos, hI⟩
  exact ⟨α, h0, h h1, hpos, hI⟩

/-- The change-of-modulus map `Cl⁺_{𝔣₁} → Cl⁺_{𝔣₂}` for `𝔣₁ ≤ 𝔣₂`. -/
def piMap {𝔣₁ 𝔣₂ : Ideal (𝓞 K)} (h : 𝔣₁ ≤ 𝔣₂) :
    NarrowRayClassGroup K 𝔣₁ →* NarrowRayClassGroup K 𝔣₂ :=
  QuotientGroup.map _ _ (Subgroup.inclusion (coprime_mono h)) (by
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact narrow_mono h hy)

lemma piMap_mk {𝔣₁ 𝔣₂ : Ideal (𝓞 K)} (h : 𝔣₁ ≤ 𝔣₂) (y : ↥(coprimeToModulus K 𝔣₁)) :
    piMap h (NarrowRayClassGroup.mk K 𝔣₁ y) =
      NarrowRayClassGroup.mk K 𝔣₂ ⟨y.1, coprime_mono h y.2⟩ := rfl

/-- An element lying in `w^{v_w(I)}` for every `w ∣ I` lies in `I`. -/
lemma mem_of_forall_pow {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (x : 𝓞 K)
    (h : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ I →
      x ∈ w.asIdeal ^ (Associates.mk w.asIdeal).count (Associates.mk I).factors) : x ∈ I := by
  classical
  have hfin := Ideal.finite_factors hI
  set S := hfin.toFinset
  have hprod : ∏ v ∈ S, v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors = I := by
    conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]
    rw [finprod_eq_prod_of_mulSupport_subset]
    · rfl
    · intro v hv
      rw [Set.Finite.coe_toFinset]
      simp only [Function.mem_mulSupport, HeightOneSpectrum.maxPowDividing] at hv
      show v.asIdeal ∣ I
      by_contra hd
      apply hv
      have : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0 := by
        by_contra h0; exact hd ((Associates.count_ne_zero_iff_dvd hI v.irreducible).1 h0)
      rw [this, pow_zero]
  have hinf := HeightOneSpectrum.inf_pow_eq_prod S
    (fun v => (Associates.mk v.asIdeal).count (Associates.mk I).factors) id (fun i _ j _ h => h)
  simp only [id] at hinf
  rw [← hprod, ← hinf, Submodule.mem_finsetInf]
  intro v hv
  exact h v ((Set.Finite.mem_toFinset hfin).1 hv)

lemma narrow_mem (hK : ∀ w : InfinitePlace K, w.IsComplex) {𝔣 : Ideal (𝓞 K)} {β : 𝓞 K}
    (hβ0 : β ≠ 0) (hβ1 : β - 1 ∈ 𝔣) (hc : principalUnit K β hβ0 ∈ coprimeToModulus K 𝔣) :
    NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K β hβ0, hc⟩ = 1 := by
  rw [NarrowRayClassGroup.mk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]
  exact Subgroup.subset_closure ⟨β, hβ0, hβ1, fun τ => (no_real hK τ).elim,
    principalUnit_val K β hβ0⟩

/-- The change-of-modulus map is onto. -/
theorem piMap_surjective (hK : ∀ w : InfinitePlace K, w.IsComplex) {𝔣₁ 𝔣₂ : Ideal (𝓞 K)}
    (h𝔣₁ : 𝔣₁ ≠ ⊥) (h : 𝔣₁ ≤ 𝔣₂) : Function.Surjective (piMap (K := K) h) := by
  classical
  have h𝔣₂ : 𝔣₂ ≠ ⊥ := fun h0 => h𝔣₁ (eq_bot_iff.2 (h0 ▸ h))
  intro C
  refine mem_of_primeClass (piMap h).range (fun v hv => ?_) C
  by_cases hv1 : v.asIdeal ∣ 𝔣₁
  swap
  · exact ⟨primeClass K 𝔣₁ v hv1, rfl⟩
  -- a generator of `v` modulo `v²`, `≡ 1` at the other primes of `𝔣₁`
  obtain ⟨ϖ, hϖ1, hϖ2⟩ := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot
    v.isPrime.ne_top 1
  set S := (Ideal.finite_factors h𝔣₁).toFinset
  have hvS : v ∈ S := (Set.Finite.mem_toFinset _).2 hv1
  obtain ⟨β, hβ⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S)
    (fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal)
    (fun w => if w = v then 2 else (Associates.mk w.asIdeal).count (Associates.mk 𝔣₁).factors)
    (fun w _ => Ideal.prime_of_isPrime w.ne_bot w.isPrime)
    (fun i _ j _ hij h' => hij (HeightOneSpectrum.ext h'))
    (fun w => if w.1 = v then ϖ else 1)
  have hβv := hβ v hvS
  simp only [if_pos rfl] at hβv
  rw [pow_one] at hϖ1
  have hβmem : β ∈ v.asIdeal := by
    have := Ideal.add_mem _ (Ideal.pow_le_self (by norm_num) hβv) hϖ1
    simpa using this
  have hβ2 : β ∉ v.asIdeal ^ 2 := fun hb => hϖ2 (by
    have := Ideal.sub_mem _ hb hβv
    simpa using this)
  have hβ0 : β ≠ 0 := fun h0 => hβ2 (h0 ▸ Ideal.zero_mem _)
  have hβw : ∀ w ∈ S, w ≠ v →
      β - 1 ∈ w.asIdeal ^ (Associates.mk w.asIdeal).count (Associates.mk 𝔣₁).factors := by
    intro w hw hwv
    have := hβ w hw
    simpa [if_neg hwv] using this
  have hβ1 : β - 1 ∈ 𝔣₂ := by
    refine mem_of_forall_pow h𝔣₂ _ fun w hw => ?_
    have hw1 : w.asIdeal ∣ 𝔣₁ := dvd_trans hw (Ideal.dvd_iff_le.2 h)
    have hwv : w ≠ v := fun hwv => hv (hwv ▸ hw)
    have hle : (Associates.mk w.asIdeal).count (Associates.mk 𝔣₂).factors ≤
        (Associates.mk w.asIdeal).count (Associates.mk 𝔣₁).factors :=
      Associates.count_le_count_of_le (Associates.mk_ne_zero.2 h𝔣₁) w.associates_irreducible
        (Associates.mk_le_mk_iff_dvd.2 (Ideal.dvd_iff_le.2 h))
    exact Ideal.pow_le_pow_right hle (hβw w ((Set.Finite.mem_toFinset _).2 hw1) hwv)
  -- `(β) = v J` with `J` prime to `𝔣₁`
  obtain ⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {β} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hβmem
  have hJ0 : J ≠ ⊥ := by
    intro h0; rw [h0, Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hJ; exact hβ0 hJ
  have hJcop : J ⊔ 𝔣₁ = ⊤ := by
    rw [T12A.sup_eq_top_iff_forall hJ0]
    intro w hw hwJ
    by_cases hwv : w = v
    · subst hwv
      apply hβ2
      rw [← Ideal.span_singleton_le_iff_mem, hJ, sq]
      exact Ideal.mul_mono_right (Ideal.le_of_dvd hwJ)
    · have hwβ : β ∈ w.asIdeal := by
        rw [← Ideal.span_singleton_le_iff_mem, hJ]
        exact le_trans Ideal.mul_le_right (Ideal.le_of_dvd hwJ)
      have h1 := hβw w ((Set.Finite.mem_toFinset _).2 hw) hwv
      have hc : 1 ≤ (Associates.mk w.asIdeal).count (Associates.mk 𝔣₁).factors := by
        rw [Nat.one_le_iff_ne_zero]
        exact (Associates.count_ne_zero_iff_dvd h𝔣₁ w.irreducible).2 hw
      have h1' := Ideal.pow_le_self (Nat.one_le_iff_ne_zero.1 hc) h1
      have := Ideal.sub_mem _ hwβ h1'
      simp at this
      exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have hJmem : J ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero hJ0
  have hJc1 : FractionalIdeal.mk0 K ⟨J, hJmem⟩ ∈ coprimeToModulus K 𝔣₁ :=
    (T12A.mk0_mem_coprimeToModulus_iff hJmem).2 hJcop
  have hJc2 := coprime_mono h hJc1
  have hpc : principalUnit K β hβ0 ∈ coprimeToModulus K 𝔣₂ :=
    principalUnit_mem_coprimeToModulus K hβ0 hβ1
  have hsplit : (⟨principalUnit K β hβ0, hpc⟩ : ↥(coprimeToModulus K 𝔣₂)) =
      ⟨primeUnit K v, primeUnit_mem_coprimeToModulus K hv⟩ * ⟨FractionalIdeal.mk0 K ⟨J, hJmem⟩, hJc2⟩ := by
    apply Subtype.ext; apply Units.ext
    show ((principalUnit K β hβ0 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (primeUnit K v : FractionalIdeal (𝓞 K)⁰ K) * (FractionalIdeal.mk0 K ⟨J, hJmem⟩ : FractionalIdeal (𝓞 K)⁰ K)
    rw [principalUnit_val, primeUnit_val, FractionalIdeal.coe_mk0, hJ, FractionalIdeal.coeIdeal_mul]
  have h1 := narrow_mem hK hβ0 hβ1 hpc
  rw [hsplit, map_mul] at h1
  refine ⟨(NarrowRayClassGroup.mk K 𝔣₁ ⟨FractionalIdeal.mk0 K ⟨J, hJmem⟩, hJc1⟩)⁻¹, ?_⟩
  rw [map_inv, piMap_mk]
  exact (eq_inv_of_mul_eq_one_left h1).symm

/-- The units `(a/b)` with `a ≡ b (mod 𝔣)`, `b` prime to `𝔣`. -/
def Good (𝔣 : Ideal (𝓞 K)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Prop :=
  ∃ a b : 𝓞 K, a ≠ 0 ∧ b ≠ 0 ∧ Ideal.span {b} ⊔ 𝔣 = ⊤ ∧ a - b ∈ 𝔣 ∧
    (I : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b)

lemma span_sup_of_sub {𝔣 : Ideal (𝓞 K)} {a b : 𝓞 K} (hb : Ideal.span {b} ⊔ 𝔣 = ⊤)
    (hab : a - b ∈ 𝔣) : Ideal.span {a} ⊔ 𝔣 = ⊤ := by
  rw [eq_top_iff, ← hb]
  refine sup_le ?_ le_sup_right
  rw [Ideal.span_singleton_le_iff_mem]
  have : b = a - (a - b) := by ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)) (Ideal.mem_sup_right hab)

lemma good_of_mem (𝔣 : Ideal (𝓞 K)) {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hI : I ∈ narrowRaySubgroup K 𝔣) : Good 𝔣 I := by
  have hK0 : ∀ x : 𝓞 K, x ≠ 0 → algebraMap (𝓞 K) K x ≠ 0 := fun x hx =>
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hx
  induction hI using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, h0, h1, -, hx⟩ := hx
    refine ⟨α, 1, h0, one_ne_zero, by rw [Ideal.span_singleton_one, top_sup_eq], h1, ?_⟩
    rw [hx, FractionalIdeal.coeIdeal_span_singleton, map_one, div_one]
  | one =>
    refine ⟨1, 1, one_ne_zero, one_ne_zero, by rw [Ideal.span_singleton_one, top_sup_eq],
      by simp, ?_⟩
    rw [Units.val_one, map_one, div_one, FractionalIdeal.spanSingleton_one]
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, ha, hb, hbc, hab, hx⟩ := hx
    obtain ⟨a', b', ha', hb', hbc', hab', hy⟩ := hy
    refine ⟨a * a', b * b', mul_ne_zero ha ha', mul_ne_zero hb hb', ?_, ?_, ?_⟩
    · rw [← Ideal.span_singleton_mul_span_singleton, C3A.sup_mul_eq_top_iff]; exact ⟨hbc, hbc'⟩
    · have : a * a' - b * b' = a * (a' - b') + (a - b) * b' := by ring
      rw [this]; exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hab') (Ideal.mul_mem_right _ _ hab)
    · rw [Units.val_mul, hx, hy, FractionalIdeal.spanSingleton_mul_spanSingleton, map_mul, map_mul]
      congr 1; field_simp
  | inv x _ hx =>
    obtain ⟨a, b, ha, hb, hbc, hab, hx⟩ := hx
    refine ⟨b, a, hb, ha, span_sup_of_sub hbc hab, ?_, ?_⟩
    · have : b - a = -(a - b) := by ring
      rw [this]; exact (Ideal.neg_mem_iff _).2 hab
    · rw [Units.val_inv_eq_inv_val, hx, FractionalIdeal.spanSingleton_inv, inv_div]

/-- Classes in the kernel of `π` are classes of `(a')(β)⁻¹` with `a', β ≡ 1 (mod 𝔣₂)` prime to `𝔣₁`. -/
theorem descend (hK : ∀ w : InfinitePlace K, w.IsComplex) {𝔣₁ 𝔣₂ : Ideal (𝓞 K)}
    (h𝔣₁ : 𝔣₁ ≠ ⊥) (h : 𝔣₁ ≤ 𝔣₂) (χ₁ : NarrowRayClassGroup K 𝔣₁ →* ℂ)
    (hχ : ∀ (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔣₁),
      α - 1 ∈ 𝔣₂ → χ₁ (NarrowRayClassGroup.mk K 𝔣₁ ⟨principalUnit K α hα, hc⟩) = 1) :
    ∃ χ₂ : NarrowRayClassGroup K 𝔣₂ →* ℂ, ∀ x, χ₂ (piMap h x) = χ₁ x := by
  classical
  have hK0 : ∀ x : 𝓞 K, x ≠ 0 → algebraMap (𝓞 K) K x ≠ 0 := fun x hx =>
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hx
  set χu := χ₁.toHomUnits
  have hker : (piMap (K := K) h).ker ≤ χu.ker := by
    intro C hC
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective C
    rw [MonoidHom.mem_ker] at hC ⊢
    have hC' : piMap h (NarrowRayClassGroup.mk K 𝔣₁ y) = 1 := hC
    rw [piMap_mk, NarrowRayClassGroup.mk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hC'
    obtain ⟨a, b, ha, hb, hbc, hab, hy⟩ := good_of_mem 𝔣₂ hC'
    set x : K := algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b
    have hx0 : x ≠ 0 := div_ne_zero (hK0 a ha) (hK0 b hb)
    have hcop : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣₁ →
        FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) = 0 := by
      intro v hv
      rw [← hy]; exact ((mem_coprimeToModulus_iff K).1 y.2) v hv
    obtain ⟨β, hβ0, hβ1, a', ha'⟩ := movingLemma K h𝔣₁ x hx0 hcop
    have ha'0 : a' ≠ 0 := by
      intro h0; rw [h0, map_zero] at ha'
      exact mul_ne_zero (hK0 β hβ0) hx0 ha'.symm
    -- `a' − β ∈ 𝔣₂`
    have hmul : (a' - β) * b = β * (a - b) := by
      apply IsFractionRing.injective (𝓞 K) K
      simp only [map_mul, map_sub, ha', x]
      field_simp [hK0 b hb]
    have hdiff : a' - β ∈ 𝔣₂ := by
      have hm : (a' - β) * b ∈ 𝔣₂ := by rw [hmul]; exact Ideal.mul_mem_left _ _ hab
      have h1 : (1 : 𝓞 K) ∈ Ideal.span {b} ⊔ 𝔣₂ := by rw [hbc]; trivial
      obtain ⟨t, ht, f, hf, htf⟩ := Submodule.mem_sup.1 h1
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ht
      have : a' - β = c * ((a' - β) * b) + (a' - β) * f := by
        rw [← mul_one (a' - β)]; nth_rewrite 1 [← htf]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hf)
    have ha'1 : a' - 1 ∈ 𝔣₂ := by
      have : a' - 1 = (a' - β) + (β - 1) := by ring
      rw [this]; exact Ideal.add_mem _ hdiff (h hβ1)
    have hcβ : principalUnit K β hβ0 ∈ coprimeToModulus K 𝔣₁ :=
      principalUnit_mem_coprimeToModulus K hβ0 hβ1
    have hsplit : principalUnit K a' ha'0 = principalUnit K β hβ0 * (y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := by
      apply Units.ext
      rw [Units.val_mul, principalUnit_val, principalUnit_val, hy,
        FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
        FractionalIdeal.spanSingleton_mul_spanSingleton, ha']
    have hca' : principalUnit K a' ha'0 ∈ coprimeToModulus K 𝔣₁ := by
      rw [hsplit]; exact mul_mem hcβ y.2
    have e1 := hχ a' ha'0 hca' ha'1
    have e2 := hχ β hβ0 hcβ (h hβ1)
    have hsub : (⟨principalUnit K a' ha'0, hca'⟩ : ↥(coprimeToModulus K 𝔣₁)) =
        ⟨principalUnit K β hβ0, hcβ⟩ * y := Subtype.ext hsplit
    rw [hsub, map_mul, map_mul, e2, one_mul] at e1
    apply Units.ext
    simp only [χu, MonoidHom.coe_toHomUnits, Units.val_one]
    exact e1
  set e := QuotientGroup.quotientKerEquivOfSurjective (piMap (K := K) h) (piMap_surjective hK h𝔣₁ h)
  refine ⟨(Units.coeHom ℂ).comp ((QuotientGroup.lift _ χu hker).comp e.symm.toMonoidHom), ?_⟩
  intro x
  have : e.symm (piMap h x) = (x : _ ⧸ (piMap (K := K) h).ker) := by
    rw [MulEquiv.symm_apply_eq]; rfl
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this, QuotientGroup.lift_mk,
    Units.coeHom_apply, χu, MonoidHom.coe_toHomUnits]

/-- **Primitive reduction.** -/
theorem exists_primitive (hK : ∀ w : InfinitePlace K, w.IsComplex) {𝔤 : Ideal (𝓞 K)}
    (h𝔤 : 𝔤 ≠ ⊥) (ω : NarrowRayClassGroup K 𝔤 →* ℂ) :
    ∃ (𝔣 : Ideal (𝓞 K)) (h : 𝔤 ≤ 𝔣) (χ₀ : NarrowRayClassGroup K 𝔣 →* ℂ),
      (∀ x, χ₀ (piMap h x) = ω x) ∧
      (∀ (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔤),
        α - 1 ∈ 𝔣 → ω (NarrowRayClassGroup.mk K 𝔤 ⟨principalUnit K α hα, hc⟩) = 1) ∧
      (∀ 𝔣' : Ideal (𝓞 K), 𝔣 ≤ 𝔣' → 𝔣' ≠ 𝔣 →
        ∃ (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔣),
          α - 1 ∈ 𝔣' ∧ (∀ τ : K →+* ℝ, 0 < τ (α : K)) ∧
            χ₀ (NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K α hα, hc⟩) ≠ 1) := by
  classical
  set D : Set (Ideal (𝓞 K)) := {𝔣 | 𝔤 ≤ 𝔣 ∧ ∀ (α : 𝓞 K) (hα : α ≠ 0)
    (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔤),
      α - 1 ∈ 𝔣 → ω (NarrowRayClassGroup.mk K 𝔤 ⟨principalUnit K α hα, hc⟩) = 1}
  have hfin : D.Finite := by
    refine (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) (Ideal.absNorm 𝔤)).subset ?_
    intro 𝔣 h𝔣
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]))
      (Ideal.absNorm_dvd_absNorm_of_le h𝔣.1)
  have hne : D.Nonempty := ⟨𝔤, le_rfl, fun α hα hc h1 => by
    rw [narrow_mem hK hα h1 hc, map_one]⟩
  obtain ⟨𝔣, ⟨h𝔣g, h𝔣D⟩, hmax⟩ := hfin.exists_maximal hne
  obtain ⟨χ₀, hχ₀⟩ := descend hK h𝔤 h𝔣g ω h𝔣D
  refine ⟨𝔣, h𝔣g, χ₀, hχ₀, h𝔣D, fun 𝔣' h1 h2 => ?_⟩
  by_contra hall
  push Not at hall
  apply h2
  have hD' : 𝔣' ∈ D := by
    refine ⟨h𝔣g.trans h1, fun α hα hc hα1 => ?_⟩
    have hc' := coprime_mono h𝔣g hc
    have := hall α hα hc' hα1 (fun τ => (no_real hK τ).elim)
    rw [← hχ₀, piMap_mk]
    exact this
  exact le_antisymm (hmax hD' h1) h1

end L3W

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3W_Abs: the convexity argument of L3K_Conv for an abstract Hecke `L`-function

Input: a `HeckeChar K 𝔣` (`K` totally complex) with a completed `L`-function
`Λ(s) = D^{s/2} Γ_ℂ(s)^{r₂} L(s, χ)`, a dual `Λ'(s) = D^{s/2} Γ_ℂ(s)^{r₂} conj L(conj s, χ)`,
`Λ(1 − s) = W Λ'(s)`, and polynomial growth. Output: `‖L(s)‖ ≤ C D^{1/2+δ} (1+|t|)^{3 r₂}` on
`−δ ≤ Re s ≤ 4`, `C = C(K, δ)`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace IsDedekindDomain Complex

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3W

open L3K

variable {K : Type} [Field K] [NumberField K]

/-- The functional-equation hypothesis. -/
def FEHyp {𝔣 : Ideal (𝓞 K)} (χ : HeckeChar K 𝔣) (D : ℝ) : Prop :=
  ∃ (W : ℂ) (Λ Λ' : ℂ → ℂ), W ≠ 0 ∧ Differentiable ℂ Λ ∧ Differentiable ℂ Λ' ∧
    (∀ s : ℂ, 1 < s.re →
      Λ s = (D : ℂ) ^ (s / 2) * Gammaℂ s ^ nrComplexPlaces K * χ.LSeries s ∧
      Λ' s = (D : ℂ) ^ (s / 2) * Gammaℂ s ^ nrComplexPlaces K *
        (starRingEnd ℂ) (χ.LSeries ((starRingEnd ℂ) s))) ∧
    ∀ s : ℂ, Λ (1 - s) = W * Λ' s

/-- The growth hypothesis. -/
def GrowthH {𝔣 : Ideal (𝓞 K)} (χ : HeckeChar K 𝔣) (δ : ℝ) : Prop :=
  ∀ L : ℂ → ℂ, Differentiable ℂ L → (∀ s : ℂ, 1 < s.re → L s = χ.LSeries s) →
    ∃ (A : ℝ) (N : ℕ), ∀ w : ℂ, -δ ≤ w.re → w.re ≤ 1 + δ → ‖L w‖ ≤ A * (1 + |w.im|) ^ N

lemma gammaC_ne_zero {s : ℂ} (hs : 0 < s.re) : Gammaℂ s ≠ 0 := by
  rw [Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero_of_re_pos hs)
  rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h
  exact absurd h (by simp [Real.pi_ne_zero])

lemma norm_heckeLSeries_le {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (χ : HeckeChar K 𝔣) {σ : ℝ}
    (hσ : 1 < σ) {s : ℂ} (hs : σ ≤ s.re) : ‖χ.LSeries s‖ ≤ Zsum K σ := by
  have hχ := T12A.norm_heckeChar_le h𝔣 χ
  rw [T12B.lseries_eq_tsum _ hχ (by linarith)]
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact (T12B.summable_absNorm_rpow hσ).of_nonneg_of_le (fun _ => norm_nonneg _)
      (T12B.norm_gs_le _ hχ hs)
  · exact Summable.tsum_le_tsum (T12B.norm_gs_le _ hχ hs)
      ((T12B.summable_absNorm_rpow hσ).of_nonneg_of_le (fun _ => norm_nonneg _)
        (T12B.norm_gs_le _ hχ hs)) (T12B.summable_absNorm_rpow hσ)

/-- **FE package**: `Λ(1 − s) = W conj Λ(conj s)` with `‖W‖ = 1`. -/
theorem fe_package' {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (χ : HeckeChar K 𝔣) {D : ℝ} (hD : 1 ≤ D)
    (hfe0 : FEHyp χ D) :
    ∃ (W : ℂ) (Λ : ℂ → ℂ), ‖W‖ = 1 ∧ Differentiable ℂ Λ ∧
      (∀ s : ℂ, 1 < s.re → Λ s = (D : ℂ) ^ (s / 2) * Gammaℂ s ^ nrComplexPlaces K * χ.LSeries s) ∧
      ∀ s : ℂ, Λ (1 - s) = W * (starRingEnd ℂ) (Λ ((starRingEnd ℂ) s)) := by
  obtain ⟨W, Λ, Λ', -, hΛ, hΛ', hre, hfe⟩ := hfe0
  have hcc : Differentiable ℂ (fun s => (starRingEnd ℂ) (Λ ((starRingEnd ℂ) s))) := fun s => by
    have := (hΛ ((starRingEnd ℂ) s)).conj_conj
    rw [RCLike.conj_conj] at this
    exact this
  have hΛ'eq : Λ' = fun s => (starRingEnd ℂ) (Λ ((starRingEnd ℂ) s)) := by
    refine entire_ext hΛ' hcc fun s hs => ?_
    have hs' : 1 < ((starRingEnd ℂ) s).re := by simpa using hs
    rw [(hre s hs).2, (hre _ hs').1, map_mul, map_mul, map_pow, ← Gammaℂ_conj, RCLike.conj_conj,
      show (starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (s / 2) by rw [map_div₀, map_ofNat],
      ofReal_cpow_conj (zero_le_one.trans hD)]
  have hfe' : ∀ s, Λ (1 - s) = W * (starRingEnd ℂ) (Λ ((starRingEnd ℂ) s)) := fun s => by
    rw [hfe s, hΛ'eq]
  have h2 : Λ 2 ≠ 0 := by
    rw [(hre 2 (by norm_num)).1]
    refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ (gammaC_ne_zero (by norm_num))))
      (C3A.euler1 χ 2 (T12A.norm_heckeChar_le h𝔣 χ) (by norm_num)).2
    rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h
    exact absurd (Complex.ofReal_eq_zero.1 h) (by linarith)
  refine ⟨W, Λ, ?_, hΛ, fun s hs => (hre s hs).1, hfe'⟩
  have e1 := hfe' (-1)
  have e2 := hfe' 2
  norm_num at e1 e2
  have hc2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  rw [hc2] at e2
  have : Λ 2 = W * (starRingEnd ℂ) W * Λ 2 := by
    calc Λ 2 = W * (starRingEnd ℂ) (Λ (-1)) := e1
      _ = W * (starRingEnd ℂ) (W * (starRingEnd ℂ) (Λ 2)) := by rw [e2]
      _ = W * (starRingEnd ℂ) W * Λ 2 := by rw [map_mul, RCLike.conj_conj]; ring
  have hW : W * (starRingEnd ℂ) W = 1 := mul_right_cancel₀ h2 (this.symm.trans (one_mul (Λ 2)).symm)
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hW
  have : ‖W‖ ^ 2 = 1 := by exact_mod_cast hW
  nlinarith [norm_nonneg W, sq_nonneg (‖W‖ - 1)]

/-- **Convexity for an abstract Hecke `L`-function.** -/
theorem abs_convexity (K : Type) [Field K] [NumberField K] {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (𝔣 : Ideal (𝓞 K)) (_ : 𝔣 ≠ ⊥) (χ : HeckeChar K 𝔣) (D : ℝ), 1 ≤ D →
      FEHyp χ D → GrowthH χ δ →
      ∃ L : ℂ → ℂ, Differentiable ℂ L ∧ (∀ s : ℂ, 1 < s.re → L s = χ.LSeries s) ∧
        ∀ s : ℂ, -δ ≤ s.re → s.re ≤ 4 →
          ‖L s‖ ≤ C * D ^ (1 / 2 + δ) * (1 + |s.im|) ^ (3 * (nrComplexPlaces K : ℝ)) := by
  set r := nrComplexPlaces K
  obtain ⟨Cpl, hCpl, hPL⟩ := PhragmenLindelof.exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip
    (-δ) (1 + δ) (3 * r : ℝ) (by linarith) (by positivity)
  set G := 4 * Real.exp Real.pi * Real.Gamma (1 + δ) ^ 2
  set G1 := max G 1
  set Z := Zsum K (1 + δ)
  have hZ : 0 ≤ Z := Zsum_nonneg _
  have hG1 : 1 ≤ G1 := le_max_right _ _
  refine ⟨Cpl * G1 ^ r * Z + Z, by positivity, ?_⟩
  intro 𝔣 h𝔣 χ D hD hfe0 hgr
  obtain ⟨W, Λ, hW, hΛ, hΛre, hfe⟩ := fe_package' h𝔣 χ hD hfe0
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hDc : ((D : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hDpos.ne'
  set L : ℂ → ℂ := fun s => Λ s * ((D : ℝ) : ℂ) ^ (-s / 2) * ((Gammaℂ s)⁻¹) ^ r
  have hL : Differentiable ℂ L := by
    refine (hΛ.mul ?_).mul (differentiable_Gammaℂ_inv.pow _)
    intro s
    exact ((differentiableAt_id.neg).div_const 2).const_cpow (Or.inl hDc)
  have hLre : ∀ s : ℂ, 1 < s.re → L s = χ.LSeries s := by
    intro s hs
    have hG := gammaC_ne_zero (s := s) (by linarith)
    show Λ s * _ * _ = _
    rw [hΛre s hs]
    have hc : ((D : ℝ) : ℂ) ^ (s / 2) * ((D : ℝ) : ℂ) ^ (-s / 2) = 1 := by
      rw [← Complex.cpow_add _ _ hDc, show s / 2 + -s / 2 = 0 by ring, Complex.cpow_zero]
    have hg : Gammaℂ s ^ r * (Gammaℂ s)⁻¹ ^ r = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hG, one_pow]
    calc _ = (((D : ℝ) : ℂ) ^ (s / 2) * ((D : ℝ) : ℂ) ^ (-s / 2)) *
          (Gammaℂ s ^ r * (Gammaℂ s)⁻¹ ^ r) * χ.LSeries s := by ring
      _ = _ := by rw [hc, hg, one_mul, one_mul]
  have hright : ∀ z : ℂ, 1 + δ ≤ z.re → ‖L z‖ ≤ Z := fun z hz => by
    rw [hLre z (by linarith)]; exact norm_heckeLSeries_le h𝔣 χ (by linarith) hz
  -- the left edge
  have hleft : ∀ z : ℂ, z.re = -δ →
      ‖L z‖ ≤ D ^ (1 / 2 + δ) * (G * (1 + |z.im|) ^ 3) ^ r * Z := by
    intro z hz
    set u := (starRingEnd ℂ) (1 - z) with hu
    have hure : u.re = 1 + δ := by simp [hu, hz]
    have hΛz : Λ z = W * (starRingEnd ℂ) (Λ u) := by
      have := hfe (1 - z); rwa [sub_sub_cancel] at this
    show ‖Λ z * _ * _‖ ≤ _
    rw [hΛz, hΛre u (by rw [hure]; linarith)]
    simp only [norm_mul, norm_pow, Complex.norm_conj, hW, one_mul, norm_inv]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hDpos, Complex.norm_cpow_eq_rpow_re_of_pos hDpos]
    have hr1 : (u / 2).re = (1 + δ) / 2 := by simp [hure]
    have hr2 : (-z / 2).re = δ / 2 := by simp [hz]
    rw [hr1, hr2]
    have hGu : ‖Gammaℂ u‖ = ‖Gammaℂ (1 - z)‖ := by rw [hu, Gammaℂ_conj, Complex.norm_conj]
    rw [hGu]
    have hratio := norm_Gammaℂ_ratio_le hδ0 (by linarith) hz
    rw [norm_div] at hratio
    have hLS := norm_heckeLSeries_le h𝔣 χ (σ := 1 + δ) (by linarith) (le_of_eq hure.symm)
    have hDD : D ^ ((1 + δ) / 2) * D ^ (δ / 2) = D ^ (1 / 2 + δ) := by
      rw [← Real.rpow_add hDpos]; congr 1; ring
    calc D ^ ((1 + δ) / 2) * ‖Gammaℂ (1 - z)‖ ^ r * ‖χ.LSeries u‖ * D ^ (δ / 2) *
          ‖Gammaℂ z‖⁻¹ ^ r
        = (D ^ ((1 + δ) / 2) * D ^ (δ / 2)) * (‖Gammaℂ (1 - z)‖ / ‖Gammaℂ z‖) ^ r *
            ‖χ.LSeries u‖ := by rw [div_pow, div_eq_mul_inv, inv_pow]; ring
      _ ≤ D ^ (1 / 2 + δ) * (G * (1 + |z.im|) ^ 3) ^ r * Z := by
          rw [hDD]
          apply mul_le_mul (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hratio _) (by positivity)) hLS (norm_nonneg _)
            (by positivity)
  set M0 := D ^ (1 / 2 + δ) * G1 ^ r * Z
  have hDp1 : 1 ≤ D ^ (1 / 2 + δ) := Real.one_le_rpow hD (by linarith)
  have hpow : ∀ t : ℝ, (1 + |t|) ^ (3 * r : ℝ) = ((1 + |t|) ^ 3) ^ r := fun t => by
    rw [← pow_mul, ← Real.rpow_natCast]; push_cast; ring_nf
  have hone : ∀ t : ℝ, 1 ≤ (1 + |t|) ^ (3 * r : ℝ) := fun t =>
    Real.one_le_rpow (by linarith [abs_nonneg t]) (by positivity)
  have hstrip : ∀ z : ℂ, -δ ≤ z.re → z.re ≤ 1 + δ →
      ‖L z‖ ≤ Cpl * M0 * (1 + |z.im|) ^ (3 * r : ℝ) := by
    refine hPL L M0 (by positivity) hL.diffContOnCl ?_ ?_ ?_
    · obtain ⟨A0, N0, hA0⟩ := hgr L hL hLre
      refine ⟨1, by
        rw [lt_div_iff₀ (by linarith)]; linarith [Real.pi_gt_three], max A0 0 + N0, fun z h1 h2 => ?_⟩
      calc ‖L z‖ ≤ A0 * (1 + |z.im|) ^ N0 := hA0 z h1.le h2.le
        _ ≤ max A0 0 * (1 + |z.im|) ^ N0 :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ Real.exp ((max A0 0 + N0) * Real.exp |z.im|) :=
            poly_le_exp_exp (le_max_right _ _) N0 _ (abs_nonneg _)
        _ = Real.exp ((max A0 0 + N0) * Real.exp (1 * |z.im|)) := by rw [one_mul]
    · intro z hz
      refine (hleft z hz).trans ?_
      rw [hpow]
      have : (G * (1 + |z.im|) ^ 3) ^ r ≤ G1 ^ r * ((1 + |z.im|) ^ 3) ^ r := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) _
      calc D ^ (1 / 2 + δ) * (G * (1 + |z.im|) ^ 3) ^ r * Z
          ≤ D ^ (1 / 2 + δ) * (G1 ^ r * ((1 + |z.im|) ^ 3) ^ r) * Z := by gcongr
        _ = M0 * ((1 + |z.im|) ^ 3) ^ r := by ring
    · intro z hz
      refine (hright z hz.ge).trans ?_
      have h1 : 1 ≤ G1 ^ r := one_le_pow₀ hG1
      have := hone z.im
      calc Z = 1 * 1 * Z * 1 := by ring
        _ ≤ D ^ (1 / 2 + δ) * G1 ^ r * Z * (1 + |z.im|) ^ (3 * r : ℝ) := by gcongr
  refine ⟨L, hL, hLre, fun z h1 h2 => ?_⟩
  have hone' := hone z.im
  rcases le_or_gt z.re (1 + δ) with h | h
  · refine (hstrip z h1 h).trans ?_
    calc Cpl * M0 * (1 + |z.im|) ^ (3 * r : ℝ)
        = Cpl * G1 ^ r * Z * D ^ (1 / 2 + δ) * (1 + |z.im|) ^ (3 * r : ℝ) := by ring
      _ ≤ (Cpl * G1 ^ r * Z + Z) * D ^ (1 / 2 + δ) * (1 + |z.im|) ^ (3 * r : ℝ) := by
          gcongr; linarith
  · refine (hright z h.le).trans ?_
    calc Z = (0 + Z) * 1 * 1 := by ring
      _ ≤ (Cpl * G1 ^ r * Z + Z) * D ^ (1 / 2 + δ) * (1 + |z.im|) ^ (3 * r : ℝ) := by
          gcongr; positivity

end L3W

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3W_RConv: convexity for a primitive narrow ray class character

For `K` totally complex and a primitive `χ₀ ≠ 1` mod `𝔣`: the Hecke character `rayH χ₀`
(`I ↦ χ₀([I])`), its functional equation from 20eaffa1, growth from c46e3955, and the bound
`‖L(s)‖ ≤ C (|d_K| N𝔣)^{1/2+δ} (1+|t|)^{3r₂}` (L3W_Abs). -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply nonZeroDivisors
  AutomorphicForm NumberField.TateGlobal Complex

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3W

variable {K : Type} [Field K] [NumberField K]

lemma chi_ne_zero {𝔣 : Ideal (𝓞 K)} (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (C : NarrowRayClassGroup K 𝔣) :
    χ C ≠ 0 := by
  intro h
  have : χ C * χ C⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [h, zero_mul] at this; exact zero_ne_one this

open Classical in
/-- The Hecke character `I ↦ χ([I])` of a narrow ray class character (`K` totally complex). -/
def rayH (hK : ∀ w : InfinitePlace K, w.IsComplex) {𝔣 : Ideal (𝓞 K)}
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) : HeckeChar K 𝔣 where
  toFun I := if I ≠ ⊥ ∧ I ⊔ 𝔣 = ⊤ then χ (T12A.cls 𝔣 I) else 0
  map_mul' I J := by
    have hb : I * J ≠ ⊥ ↔ I ≠ ⊥ ∧ J ≠ ⊥ := by
      simp only [ne_eq, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
    by_cases hI : I ≠ ⊥ ∧ I ⊔ 𝔣 = ⊤ <;> by_cases hJ : J ≠ ⊥ ∧ J ⊔ 𝔣 = ⊤
    · have hIJ : I * J ≠ ⊥ ∧ I * J ⊔ 𝔣 = ⊤ :=
        ⟨hb.2 ⟨hI.1, hJ.1⟩, C3A.sup_mul_eq_top_iff.2 ⟨hI.2, hJ.2⟩⟩
      rw [if_pos hIJ, if_pos hI, if_pos hJ, L3K.cls_mul hI hJ hIJ, map_mul]
    · rw [if_neg hJ, mul_zero, if_neg]
      rintro ⟨h1, h2⟩; exact hJ ⟨(hb.1 h1).2, (C3A.sup_mul_eq_top_iff.1 h2).2⟩
    · rw [if_neg hI, zero_mul, if_neg]
      rintro ⟨h1, h2⟩; exact hI ⟨(hb.1 h1).1, (C3A.sup_mul_eq_top_iff.1 h2).1⟩
    · rw [if_neg hI, zero_mul, if_neg]
      rintro ⟨h1, h2⟩; exact hI ⟨(hb.1 h1).1, (C3A.sup_mul_eq_top_iff.1 h2).1⟩
  eq_zero_iff' I := by
    split_ifs with h
    · simp only [chi_ne_zero, false_iff, not_or, not_not]; exact h
    · simp only [true_iff]; by_contra h'; push Not at h'; exact h h'
  map_principal' α hα h1 := by
    have hc : Ideal.span {α} ≠ ⊥ ∧ Ideal.span {α} ⊔ 𝔣 = ⊤ :=
      ⟨T12A.span_ne_bot hα, T12A.span_sup_eq_top h1⟩
    rw [if_pos hc, T12A.cls, dif_pos hc]
    have hpc : principalUnit K α hα ∈ coprimeToModulus K 𝔣 :=
      (T12A.mk0_mem_coprimeToModulus_iff _).2 hc.2
    have := narrow_mem hK hα h1 hpc
    refine (congrArg χ ((congrArg (NarrowRayClassGroup.mk K 𝔣) (Subtype.ext rfl)).trans this)).trans
      (map_one _)

lemma rayH_prime (hK : ∀ w : InfinitePlace K, w.IsComplex) {𝔣 : Ideal (𝓞 K)}
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣) :
    (rayH hK χ).toFun v.asIdeal = χ (primeClass K 𝔣 v hv) := by
  classical
  have h1 : v.asIdeal ≠ ⊥ ∧ v.asIdeal ⊔ 𝔣 = ⊤ := ⟨v.ne_bot, (L3K.sup_eq_top_iff_not_dvd v _).2 hv⟩
  show (if _ then _ else _) = _
  rw [if_pos h1, T12A.cls, dif_pos h1]
  rfl

/-- Two characters agreeing on prime classes are equal. -/
lemma ext_primeClass {𝔣 : Ideal (𝓞 K)} (χ₁ χ₂ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (h : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣),
      χ₁ (primeClass K 𝔣 v hv) = χ₂ (primeClass K 𝔣 v hv)) : χ₁ = χ₂ := by
  have hH := mem_of_primeClass (MonoidHom.eqLocus χ₁.toHomUnits χ₂.toHomUnits) (fun v hv => by
    show χ₁.toHomUnits _ = χ₂.toHomUnits _
    apply Units.ext; simpa using h v hv)
  ext C
  have := hH C
  have := congrArg (fun x : ℂˣ => (x : ℂ)) this
  simpa using this

lemma rayChar_rayH (hK : ∀ w : InfinitePlace K, w.IsComplex) {𝔣 : Ideal (𝓞 K)}
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) : T12A.rayChar (rayH hK χ) = χ := by
  refine ext_primeClass _ _ fun v hv => ?_
  rw [← rayH_prime hK χ v hv]
  exact T12A.rayChar_mk_ideal _ _ _

lemma rayClassLSeries_eq_rayH (hK : ∀ w : InfinitePlace K, w.IsComplex) {𝔣 : Ideal (𝓞 K)}
    (h𝔣 : 𝔣 ≠ ⊥) (χ : NarrowRayClassGroup K 𝔣 →* ℂ) {s : ℂ} (hs : 1 < s.re) :
    M4aTorus.rayClassLSeries K 𝔣 χ s = (rayH hK χ).LSeries s := by
  conv_lhs => rw [← rayChar_rayH hK χ]
  exact T12A.rayClassLSeries_eq h𝔣 _ hs

lemma rayZeta_conj {𝔣 : Ideal (𝓞 K)} (C : NarrowRayClassGroup K 𝔣) (s : ℂ) :
    M4aTorus.rayZeta K 𝔣 C s = (starRingEnd ℂ) (M4aTorus.rayZeta K 𝔣 C ((starRingEnd ℂ) s)) := by
  rw [M4aTorus.rayZeta, M4aTorus.rayZeta, LSeries, LSeries, Complex.conj_tsum]
  congr 1; funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀, Complex.conj_natCast,
    L3K.natCast_cpow_conj]

lemma rayClassLSeries_conj {𝔣 : Ideal (𝓞 K)} (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (s : ℂ) :
    M4aTorus.rayClassLSeries K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) s =
      (starRingEnd ℂ) (M4aTorus.rayClassLSeries K 𝔣 χ ((starRingEnd ℂ) s)) := by
  rw [M4aTorus.rayClassLSeries, M4aTorus.rayClassLSeries, Complex.conj_tsum]
  congr 1; funext C
  rw [map_mul, rayZeta_conj C s]
  rfl

/-- The primes dividing `𝔣`. -/
def fPrimes {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (Ideal.finite_factors (R := 𝓞 K) h𝔣).toFinset

lemma mem_fPrimes {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ fPrimes h𝔣 ↔ v.asIdeal ∣ 𝔣 := by
  rw [fPrimes, Set.Finite.mem_toFinset]; rfl

def epEquiv' {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) :
    C3A.EP 𝔣 ≃ {v : HeightOneSpectrum (𝓞 K) // v ∉ fPrimes h𝔣} where
  toFun P := ⟨⟨P.1, P.2.1, P.2.2.1⟩, by
    rw [mem_fPrimes, ← L3K.sup_eq_top_iff_not_dvd]; exact P.2.2.2⟩
  invFun v := ⟨v.1.asIdeal, v.1.isPrime, v.1.ne_bot, by
    rw [L3K.sup_eq_top_iff_not_dvd, ← mem_fPrimes h𝔣]; exact v.2⟩
  left_inv P := rfl
  right_inv v := rfl

/-- **Growth.** -/
theorem growthH_rayH (hK : ∀ w : InfinitePlace K, w.IsComplex) {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (hχ1 : χ ≠ 1) (δ : ℝ) : GrowthH (rayH hK χ) δ := by
  classical
  intro L hL hLre
  set χu := χ.toHomUnits
  obtain ⟨η, hfin, hadm, hunit, hval⟩ := LT.HeckeChar.exists_heckeCharOfRayClassChar K 𝔣 χu
  have hvalC : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣),
      ((η (uniformizerIdele K v) : ℂˣ) : ℂ) = χ (primeClass K 𝔣 v hv) := by
    intro v hv
    rw [hval v hv, MonoidHom.coe_toHomUnits]
  have hnt : ∃ x ∈ normOneIdeles K, η x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t, ht⟩ := exists_eq_normPowChar_of_forall_mem_normOneIdeles K η hfin.continuous hunit hcon
    obtain ⟨n, hn, hpow⟩ := hfin.isOfFinOrder.exists_pow_eq_one
    have hval_t : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((η z : ℂˣ) : ℂ) = ((ideleNorm K z : ℝ) : ℂ) ^ (Complex.I * t) := by
      intro z; rw [ht]; rfl
    have ht0 : t = 0 := by
      by_contra ht0
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      obtain ⟨z, -, hz⟩ := exists_ideleNorm_eq_and_snd_eq_one K
        (Real.exp (Real.pi / (t * n))) (Real.exp_pos _)
      have h1 : ((η z : ℂˣ) : ℂ) ^ n = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hpow, MonoidHom.one_apply,
          Units.val_one]
      set c := Real.pi / (t * n)
      have hc : ((Real.exp c : ℝ) : ℂ) ^ (Complex.I * t) = Complex.exp (c * (Complex.I * t)) := by
        rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos c).ne'),
          ← Complex.ofReal_log (Real.exp_pos c).le, Real.log_exp]
      rw [hval_t, hz, hc, ← Complex.exp_nat_mul] at h1
      have e : (n : ℂ) * (c * (Complex.I * t)) = Real.pi * Complex.I := by
        have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
        have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
        simp only [c]; push_cast; field_simp
      rw [e, Complex.exp_pi_mul_I] at h1
      norm_num at h1
    have hη1 : ∀ z, η z = 1 := by
      intro z; apply Units.ext; rw [hval_t, ht0]; simp
    apply hχ1
    refine L3K.eq_one_of_primeClass χ fun v hv => ?_
    rw [← hvalC v hv, hη1, Units.val_one]
  have hLE : ∀ s : ℂ, 1 < s.re →
      L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ fPrimes h𝔣},
        (1 - (if IsUnramifiedCharAt η v.1 then ((η (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
    intro s hs
    have hχn := T12A.norm_heckeChar_le h𝔣 (rayH hK χ)
    rw [hLre s hs, ← (C3A.euler1 (rayH hK χ) s hχn hs).1.tprod_eq, ← (epEquiv' h𝔣).tprod_eq]
    refine tprod_congr fun P => ?_
    have hv : ¬ ((epEquiv' h𝔣 P).1).asIdeal ∣ 𝔣 := by
      rw [← mem_fPrimes h𝔣]; exact (epEquiv' h𝔣 P).2
    rw [if_pos (L3K.isUnramifiedCharAt_of_admitsModulus h𝔣 hadm hv), hvalC _ hv,
      ← rayH_prime hK χ _ hv]
    rfl
  exact exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc K η
    hfin.isIdeleClassChar hfin.continuous hunit hnt (fPrimes h𝔣) (-δ) (1 + δ) L hL hLE

/-- **The functional equation hypothesis** for a primitive `χ ≠ 1`. -/
theorem feHyp_rayH (hK : ∀ w : InfinitePlace K, w.IsComplex) {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (hχ1 : χ ≠ 1)
    (hprim : ∀ 𝔣' : Ideal (𝓞 K), 𝔣 ≤ 𝔣' → 𝔣' ≠ 𝔣 →
      ∃ (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔣),
        α - 1 ∈ 𝔣' ∧ (∀ τ : K →+* ℝ, 0 < τ (α : K)) ∧
          χ (NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K α hα, hc⟩) ≠ 1) :
    FEHyp (rayH hK χ) (|(discr K : ℝ)| * (Ideal.absNorm 𝔣 : ℝ)) := by
  have hpar : ∀ (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔣),
      α - 1 ∈ 𝔣 →
        χ (NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K α hα, hc⟩) =
          ∏ w ∈ (∅ : Finset {w : InfinitePlace K // w.IsReal}),
            ((SignType.sign (embedding_of_isReal w.2 (α : K)) : ℤ) : ℂ) := by
    intro α hα hc h1
    rw [Finset.prod_empty, narrow_mem hK hα h1 hc, map_one]
  obtain ⟨W, Λ, Λ', hW, hΛ, hΛ', hre, hfe⟩ :=
    NumberField.exists_completedRayL_functionalEquation_of_primitive K 𝔣 h𝔣 χ ∅ hpar hprim
  have hr0 : nrRealPlaces K = 0 := L3K.nrRealPlaces_eq_zero hK
  refine ⟨W, Λ, Λ', hW, hΛ, hΛ', fun s hs => ?_, hfe⟩
  obtain ⟨h1, h2⟩ := hre s hs
  have hs' : 1 < ((starRingEnd ℂ) s).re := by simpa using hs
  rw [if_neg hχ1, one_mul] at h1 h2
  constructor
  · rw [h1, M4aTorus.completedRayL, hr0, Finset.card_empty, pow_zero, pow_zero, mul_one, mul_one,
      rayClassLSeries_eq_rayH hK h𝔣 χ hs]
  · rw [h2, M4aTorus.completedRayL, hr0, Finset.card_empty, pow_zero, pow_zero, mul_one, mul_one,
      rayClassLSeries_conj, rayClassLSeries_eq_rayH hK h𝔣 χ hs']

end L3W

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_KB: the Kummer-field basics of C0Z (C0ZK, C0ZF, parts of C0ZS/ZN/ZU/ZV), copied without
the idelic Artin map, so that the KummerConvexity solution does not pull in the C0-H development. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin Polynomial

noncomputable section

namespace ArtinPrimitiveRoots.L3K.KB

section Kch


variable {F : Type} [Field F] {ℓ : ℕ} [NeZero ℓ]

/-- Every `ℓ`-th root of unity of an `F`-field comes from `F`. -/
theorem exists_of_pow_eq_one {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ) (M : Type*) [Field M] [Algebra F M]
    (x : M) (hx : x ^ ℓ = 1) : ∃ y : F, y ^ ℓ = 1 ∧ algebraMap F M y = x := by
  have hζM := hζ.map_of_injective (FaithfulSMul.algebraMap_injective F M)
  obtain ⟨i, -, hi⟩ := hζM.eq_pow_of_pow_eq_one hx
  exact ⟨ζ ^ i, by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow], by rw [map_pow, hi]⟩

variable {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ) (M : Type*) [Field M] [Algebra F M]
include hζ

/-- A Kummer generator: a nonzero `β` with `β^ℓ ∈ F`. -/
structure KGen (M : Type*) [Field M] [Algebra F M] (ℓ : ℕ) where
  β : M
  ne_zero : β ≠ 0
  pow_mem : ∃ a : F, β ^ ℓ = algebraMap F M a

variable {M}

theorem ratio_pow (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) : (σ g.β / g.β) ^ ℓ = 1 := by
  obtain ⟨a, ha⟩ := g.pow_mem
  rw [div_pow, ← map_pow, ha, AlgEquiv.commutes, ← ha, div_self (pow_ne_zero _ g.ne_zero)]

theorem ratio_mem (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) :
    ∃ y : F, y ^ ℓ = 1 ∧ algebraMap F M y = σ g.β / g.β :=
  exists_of_pow_eq_one hζ M _ (ratio_pow hζ g σ)

/-- The value of the Kummer character in `F`. -/
def kval (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) : F := (ratio_mem hζ g σ).choose

theorem kval_pow (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) : kval hζ g σ ^ ℓ = 1 :=
  (ratio_mem hζ g σ).choose_spec.1

theorem algebraMap_kval (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) :
    algebraMap F M (kval hζ g σ) = σ g.β / g.β :=
  (ratio_mem hζ g σ).choose_spec.2

theorem fix_ratio (g : KGen (F := F) M ℓ) (σ τ : M ≃ₐ[F] M) :
    σ (τ g.β / g.β) = τ g.β / g.β := by
  rw [← algebraMap_kval hζ g τ, AlgEquiv.commutes]

/-- The Kummer character `σ ↦ σβ/β`, valued in `μ_ℓ(F)`. -/
def kch (g : KGen (F := F) M ℓ) : (M ≃ₐ[F] M) →* rootsOfUnity ℓ F where
  toFun σ := rootsOfUnity.mkOfPowEq (kval hζ g σ) (kval_pow hζ g σ)
  map_one' := by
    apply Subtype.ext; apply Units.ext
    simp only [rootsOfUnity.coe_mkOfPowEq, OneMemClass.coe_one, Units.val_one]
    apply FaithfulSMul.algebraMap_injective F M
    rw [algebraMap_kval hζ, map_one, AlgEquiv.one_apply, div_self g.ne_zero]
  map_mul' σ τ := by
    apply Subtype.ext; apply Units.ext
    simp only [rootsOfUnity.coe_mkOfPowEq, Subgroup.coe_mul, Units.val_mul]
    apply FaithfulSMul.algebraMap_injective F M
    rw [map_mul, algebraMap_kval hζ, algebraMap_kval hζ, algebraMap_kval hζ, AlgEquiv.mul_apply]
    have h1 : τ g.β = (τ g.β / g.β) * g.β := by field_simp [g.ne_zero]
    conv_lhs => rw [h1, map_mul, fix_ratio hζ g σ τ]
    field_simp [g.ne_zero]

theorem algebraMap_kch (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) :
    algebraMap F M ((kch hζ g σ : Fˣ) : F) = σ g.β / g.β := by
  simp only [kch, MonoidHom.coe_mk, OneHom.coe_mk, rootsOfUnity.coe_mkOfPowEq]
  exact algebraMap_kval hζ g σ


end Kch

section KFsec


variable (F : Type) [Field F] (ℓ : ℕ)

/-- `F(a^{1/ℓ})`. -/
def KF (a : Fˣ) : Type := (X ^ ℓ - C (a : F)).SplittingField

/-- `F(a^{1/ℓ}, a'^{1/ℓ})`. -/
def KF2 (a a' : Fˣ) : Type := ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F))).SplittingField

variable (a a' : Fˣ)

instance : Field (KF F ℓ a) := inferInstanceAs (Field (SplittingField _))
instance : Algebra F (KF F ℓ a) := inferInstanceAs (Algebra F (SplittingField _))
instance : Field (KF2 F ℓ a a') := inferInstanceAs (Field (SplittingField _))
instance : Algebra F (KF2 F ℓ a a') := inferInstanceAs (Algebra F (SplittingField _))
instance : IsSplittingField F (KF F ℓ a) (X ^ ℓ - C (a : F)) :=
  inferInstanceAs (IsSplittingField F (SplittingField _) _)
instance : IsSplittingField F (KF2 F ℓ a a') ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F))) :=
  inferInstanceAs (IsSplittingField F (SplittingField _) _)
instance : FiniteDimensional F (KF F ℓ a) := IsSplittingField.finiteDimensional _ (X ^ ℓ - C (a : F))
instance : FiniteDimensional F (KF2 F ℓ a a') :=
  IsSplittingField.finiteDimensional _ ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F)))
instance : Normal F (KF F ℓ a) := Normal.of_isSplittingField (X ^ ℓ - C (a : F))
instance : Normal F (KF2 F ℓ a a') :=
  Normal.of_isSplittingField ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F)))

section CharZero

variable [CharZero F]

instance : IsGalois F (KF F ℓ a) := { }
instance : IsGalois F (KF2 F ℓ a a') := { }

end CharZero

instance [NumberField F] : NumberField (KF F ℓ a) := NumberField.of_module_finite F _
instance [NumberField F] : NumberField (KF2 F ℓ a a') := NumberField.of_module_finite F _

variable {F ℓ}

theorem exists_root_of_splits {M : Type*} [Field M] [Algebra F M] (hℓ : ℓ ≠ 0)
    (hs : Splits ((X ^ ℓ - C (a : F)).map (algebraMap F M))) : ∃ β : M, β ^ ℓ = algebraMap F M a := by
  have hdeg : ((X ^ ℓ - C (a : F)).map (algebraMap F M)).degree ≠ 0 := by
    rw [degree_map]
    exact degree_ne_of_natDegree_ne (by rw [natDegree_X_pow_sub_C]; exact hℓ)
  obtain ⟨β, hβ⟩ := hs.exists_eval_eq_zero hdeg
  refine ⟨β, ?_⟩
  simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, eval_sub, eval_pow, eval_X,
    eval_C] at hβ
  exact sub_eq_zero.mp hβ

/-- A Kummer generator from a root of `X^ℓ - a`. -/
def kgenOf {M : Type*} [Field M] [Algebra F M] {β : M} (hβ : β ^ ℓ = algebraMap F M a)
    (hℓ : ℓ ≠ 0) : KGen (F := F) M ℓ where
  β := β
  ne_zero := by
    rintro rfl
    rw [zero_pow hℓ, eq_comm, map_eq_zero] at hβ
    exact a.ne_zero hβ
  pow_mem := ⟨a, hβ⟩

theorem splits_KF (hℓ : ℓ ≠ 0) :
    Splits ((X ^ ℓ - C (a : F)).map (algebraMap F (KF F ℓ a))) :=
  IsSplittingField.splits (KF F ℓ a) (X ^ ℓ - C (a : F))

theorem root_pow_of_mem_rootSet {M : Type*} [Field M] [Algebra F M] {b : F} {r : M}
    (hr : aeval r (X ^ ℓ - C b) = 0) : r ^ ℓ = algebraMap F M b := by
  simpa [sub_eq_zero] using hr

section Comm

variable [NeZero ℓ] {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ)
include hζ

/-- A root of `X^ℓ - a` is a multiple of a fixed generator by an element of `F`. -/
theorem eq_smul_of_pow_eq {M : Type*} [Field M] [Algebra F M] (g : KGen (F := F) M ℓ) {r : M}
    (hr : r ^ ℓ = g.β ^ ℓ) : ∃ c : F, r = algebraMap F M c * g.β := by
  have h1 : (r / g.β) ^ ℓ = 1 := by rw [div_pow, hr, div_self (pow_ne_zero _ g.ne_zero)]
  obtain ⟨c, -, hc⟩ := exists_of_pow_eq_one hζ M _ h1
  exact ⟨c, by rw [hc]; field_simp [g.ne_zero]⟩

theorem fixes_of_kch_eq_one {M : Type*} [Field M] [Algebra F M] (g : KGen (F := F) M ℓ)
    (σ : M ≃ₐ[F] M) (h : kch hζ g σ = 1) : σ g.β = g.β := by
  have := algebraMap_kch hζ g σ
  rw [h, OneMemClass.coe_one, Units.val_one, map_one, eq_comm, div_eq_one_iff_eq g.ne_zero] at this
  exact this

theorem fixes_root {M : Type*} [Field M] [Algebra F M] (g : KGen (F := F) M ℓ)
    (σ : M ≃ₐ[F] M) (h : σ g.β = g.β) {r : M} (hr : r ^ ℓ = g.β ^ ℓ) : σ r = r := by
  obtain ⟨c, rfl⟩ := eq_smul_of_pow_eq hζ g hr
  rw [map_mul, AlgEquiv.commutes, h]

theorem eq_one_of_kch_KF (g : KGen (F := F) (KF F ℓ a) ℓ)
    (hg : g.β ^ ℓ = algebraMap F (KF F ℓ a) a) (σ : KF F ℓ a ≃ₐ[F] KF F ℓ a)
    (h : kch hζ g σ = 1) : σ = 1 := by
  have f1 := fixes_of_kch_eq_one hζ g σ h
  apply AlgEquiv.coe_toAlgHom_injective
  refine AlgHom.ext_of_adjoin_eq_top
    (IsSplittingField.adjoin_rootSet (KF F ℓ a) (X ^ ℓ - C (a : F))) fun r hr => ?_
  rw [mem_rootSet] at hr
  show σ r = r
  exact fixes_root hζ g σ f1 (by rw [root_pow_of_mem_rootSet hr.2]; exact hg.symm)

theorem kch_KF_injective (g : KGen (F := F) (KF F ℓ a) ℓ)
    (hg : g.β ^ ℓ = algebraMap F (KF F ℓ a) a) : Function.Injective (kch hζ g) :=
  (injective_iff_map_eq_one _).mpr fun σ h => eq_one_of_kch_KF a hζ g hg σ h

end Comm


end KFsec

section RootKF
variable (F : Type) [Field F] [NumberField F] {ℓ : ℕ} [NeZero ℓ]

/-- The chosen root of `X^ℓ - a` in `F(a^{1/ℓ})`. -/
def rootKF (a : Fˣ) : KGen (F := F) (KF F ℓ a) ℓ :=
  kgenOf a (exists_root_of_splits a (NeZero.ne ℓ) (splits_KF a (NeZero.ne ℓ))).choose_spec
    (NeZero.ne ℓ)

theorem rootKF_pow (a : Fˣ) : (rootKF F a).β ^ ℓ = algebraMap F (KF F ℓ a) a :=
  (exists_root_of_splits a (NeZero.ne ℓ) (splits_KF a (NeZero.ne ℓ))).choose_spec
end RootKF

section UV
/-- `n`-th roots of unity congruent modulo `Q` with `n ∉ Q` are equal. -/
theorem eq_of_pow_eq_one_of_sub_mem {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R) {n : ℕ}
    (hn : (n : R) ∉ Q) {a b : R} (ha : a ^ n = 1) (hb : b ^ n = 1) (hab : a - b ∈ Q) : a = b := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  set η := b * a ^ (n - 1) with hη
  have han : a ^ (n - 1) * a = 1 := by rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0), ha]
  have h1 : 1 - η ∈ Q := by
    have : 1 - η = a ^ (n - 1) * (a - b) := by
      rw [hη, mul_sub, han]; ring
    rw [this]; exact Q.mul_mem_left _ hab
  by_cases hη1 : η = 1
  · calc a = a * 1 := (mul_one a).symm
      _ = a * η := by rw [hη1]
      _ = b * (a ^ (n - 1) * a) := by rw [hη]; ring
      _ = b := by rw [han, mul_one]
  · exfalso
    have hηn : η ^ n = 1 := by
      rw [hη, mul_pow, ← pow_mul, hb, one_mul, mul_comm, pow_mul, ha, one_pow]
    have hsum : ∑ i ∈ Finset.range n, η ^ i = 0 := by
      have h := geom_sum_mul η n
      rw [hηn, sub_self] at h
      exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hη1)
    apply hn
    have : (n : R) = ∑ i ∈ Finset.range n, (1 - η ^ i) := by
      rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_const, Finset.card_range, nsmul_one]
    rw [this]
    refine Q.sum_mem fun i _ => ?_
    rw [← geom_sum_mul_neg]
    exact Q.mul_mem_left _ h1

variable (F : Type) [Field F] [NumberField F] {ℓ : ℕ} [NeZero ℓ] {ζ : F}
  (hζ : IsPrimitiveRoot ζ ℓ)

/-- An integral Kummer generator `β = d α` at a place where `a` is a unit. -/
theorem exists_intGen (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) (ha : v.valuation F (a : F) = 1) :
    ∃ (d n : 𝓞 F) (β : 𝓞 (KF F ℓ a)), d ∉ v.asIdeal ∧ n ∉ v.asIdeal ∧
      (a : F) * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F n ∧
      (β : KF F ℓ a) = algebraMap F (KF F ℓ a) (algebraMap (𝓞 F) F d) * (rootKF F a).β ∧
      β ^ ℓ = algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) (d ^ (ℓ - 1) * n) := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v (a : F) ha.le
  have hd : (d : 𝓞 F) ∉ v.asIdeal := d.2
  have hn : n ∉ v.asIdeal := by
    rw [← v.valuation_eq_one_iff_notMem (K := F), ← hnd, map_mul, ha,
      (v.valuation_eq_one_iff_notMem (K := F)).mpr hd, one_mul]
  set K := KF F ℓ a
  set β : K := algebraMap F K (algebraMap (𝓞 F) F d) * (rootKF F a).β
  have hβpow : β ^ ℓ = algebraMap F K (algebraMap (𝓞 F) F ((d : 𝓞 F) ^ (ℓ - 1) * n)) := by
    have hℓ1 : ℓ = (ℓ - 1) + 1 := (Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne ℓ))).symm
    rw [mul_pow, rootKF_pow, ← map_pow, ← map_mul]
    congr 1
    rw [map_mul, map_pow, ← hnd]
    conv_lhs => rw [hℓ1, pow_succ]
    ring
  have hint : IsIntegral ℤ β := by
    apply IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne ℓ))
    rw [hβpow, ← IsScalarTower.algebraMap_apply]
    exact ((((d : 𝓞 F) ^ (ℓ - 1) * n).isIntegral_coe).map (IsScalarTower.toAlgHom ℤ F K))
  refine ⟨d, n, ⟨β, hint⟩, hd, hn, hnd, rfl, ?_⟩
  apply RingOfIntegers.ext
  simp only [map_pow]
  show β ^ ℓ = _
  rw [hβpow, ← IsScalarTower.algebraMap_apply]
  rfl

/-- A root of unity of `F` as an algebraic integer. -/
def rootO (μ : rootsOfUnity ℓ F) : 𝓞 F :=
  ⟨((μ : Fˣ) : F), IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne ℓ)) (by
    have := μ.2; rw [mem_rootsOfUnity] at this
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]; exact isIntegral_one)⟩

omit [NumberField F] in
theorem rootO_pow (μ : rootsOfUnity ℓ F) : rootO F μ ^ ℓ = 1 := by
  apply RingOfIntegers.ext
  show ((μ : Fˣ) : F) ^ ℓ = 1
  have := μ.2; rw [mem_rootsOfUnity] at this
  rw [← Units.val_pow_eq_pow_val, this, Units.val_one]

include hζ in
/-- `σ β = μ_σ β` in `𝓞 K`. -/
theorem smul_intGen (a : Fˣ) (d : 𝓞 F) (β : 𝓞 (KF F ℓ a))
    (hβ : (β : KF F ℓ a) = algebraMap F (KF F ℓ a) (algebraMap (𝓞 F) F d) * (rootKF F a).β)
    (σ : KF F ℓ a ≃ₐ[F] KF F ℓ a) :
    σ • β = algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) (rootO F (kch hζ (rootKF F a) σ)) * β := by
  apply RingOfIntegers.ext
  have e : ∀ x : 𝓞 F, ((algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) x : 𝓞 (KF F ℓ a)) : KF F ℓ a) =
      algebraMap F (KF F ℓ a) (x : F) := fun x => rfl
  show σ (β : KF F ℓ a) = ((algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) _ : 𝓞 (KF F ℓ a)) : KF F ℓ a) *
    (β : KF F ℓ a)
  rw [e, hβ]
  show σ _ = algebraMap F (KF F ℓ a) ((kch hζ (rootKF F a) σ : Fˣ) : F) * _
  rw [algebraMap_kch, map_mul, AlgEquiv.commutes]
  field_simp [(rootKF (ℓ := ℓ) F a).ne_zero]

include hζ in
/-- **Kummer extensions are unramified** at `v ∤ ℓ` where `a` is a unit. -/
theorem inertia_eq_bot (v : HeightOneSpectrum (𝓞 F)) (hv : (ℓ : 𝓞 F) ∉ v.asIdeal) (a : Fˣ)
    (ha : v.valuation F (a : F) = 1) (w : HeightOneSpectrum (𝓞 (KF F ℓ a)))
    (hw : w.under (𝓞 F) = v) :
    w.asIdeal.inertia (KF F ℓ a ≃ₐ[F] KF F ℓ a) = ⊥ := by
  obtain ⟨d, n, β, hd, hn, -, hβ, hβpow⟩ := exists_intGen (ℓ := ℓ) F v a ha
  have hmem : ∀ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) x ∈ w.asIdeal → x ∈ v.asIdeal := by
    intro x hx; rw [← hw]; exact hx
  have hβw : β ∉ w.asIdeal := by
    intro h
    have : β ^ ℓ ∈ w.asIdeal := w.asIdeal.pow_mem_of_mem h ℓ (Nat.pos_of_ne_zero (NeZero.ne ℓ))
    rw [hβpow] at this
    have h2 := hmem _ this
    rcases v.isPrime.mem_or_mem h2 with h3 | h3
    · exact hd (v.isPrime.mem_of_pow_mem _ h3)
    · exact hn h3
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  have h1 := hσ β
  rw [smul_intGen F hζ a d β hβ σ] at h1
  have h2 : (algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) (rootO F (kch hζ (rootKF F a) σ) - 1)) * β ∈
      w.asIdeal := by rw [map_sub, map_one, sub_mul, one_mul]; exact h1
  rcases w.isPrime.mem_or_mem h2 with h3 | h3
  · have h4 := hmem _ h3
    have h5 := eq_of_pow_eq_one_of_sub_mem v.asIdeal hv (rootO_pow F _) (one_pow ℓ) h4
    apply kch_KF_injective a hζ (rootKF F a) (rootKF_pow F a)
    rw [map_one]
    apply Subtype.ext; apply Units.ext
    have := congrArg (fun z : 𝓞 F => (z : F)) h5
    exact this
  · exact absurd h3 hβw

include hζ in

/-- An algebraic integer from an element of `F` that is a root of unity. -/
def toO (x : F) (hx : x ^ ℓ = 1) : 𝓞 F :=
  ⟨x, IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne ℓ)) (by rw [hx]; exact isIntegral_one)⟩

omit [NumberField F] in
theorem toO_pow (x : F) (hx : x ^ ℓ = 1) : toO F x hx ^ ℓ = 1 := by
  apply RingOfIntegers.ext; show x ^ ℓ = 1; exact hx

include hζ in
/-- `ℓ ∣ N v - 1` when `v ∤ ℓ`. -/
theorem dvd_card_sub_one (v : HeightOneSpectrum (𝓞 F)) (hv : (ℓ : 𝓞 F) ∉ v.asIdeal) :
    ℓ ∣ Nat.card (𝓞 F ⧸ v.asIdeal) - 1 := by
  classical
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  set z := toO F ζ hζ.pow_eq_one
  have hz : z ^ ℓ = 1 := toO_pow F ζ _
  have hη : IsPrimitiveRoot (Ideal.Quotient.mk v.asIdeal z) ℓ := by
    refine ⟨by rw [← map_pow, hz, map_one], fun l hl => ?_⟩
    have h1 : z ^ l - 1 ∈ v.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hl, map_one, sub_self]
    have h2 := eq_of_pow_eq_one_of_sub_mem v.asIdeal hv
      (by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]) (one_pow ℓ) h1
    apply hζ.dvd_of_pow_eq_one
    have := congrArg (fun x : 𝓞 F => (x : F)) h2
    simpa [z, toO] using this
  have := FiniteField.pow_card_sub_one_eq_one (Ideal.Quotient.mk v.asIdeal z)
    (hη.ne_zero (NeZero.ne ℓ))
  rw [Fintype.card_eq_nat_card] at this
  exact hη.dvd_of_pow_eq_one _ this


end UV

end ArtinPrimitiveRoots.L3K.KB

end
end
end

section
section
/-! # L3K_Kum: the sextic Kummer character `ψ_a` of `F(a^{1/6})/F`

For `a ∈ Fˣ`, `M = KF F 6 a` and `ψ_a = ι ∘ kch : Gal(M/F) →* ℂˣ` (C0Z):
* `psi_injective`; `psi_ne_one` when `a` is not a sixth power in `F`;
* `isUnramifiedAt_psi`: unramified at `v ∤ 6` with `v(a) = 0` (C0ZU);
* `psi_artinFrob`: there `ψ_a(Frob_v) = ι ω` for the sixth root of unity `ω ≡ a^{(Nv−1)/6}`;
* `not_isUnramifiedAt_psi`: ramified at `v` with `6 ∤ v(a)`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin Polynomial ArtinPrimitiveRoots.L3K.KB

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

variable (F : Type) [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 6) (ι : F →+* ℂ)
  (a : Fˣ)

/-- The Kummer field `F(a^{1/6})`. -/
abbrev KM := KF F 6 a

/-- `ψ_a(σ) = ι(σβ/β)`. -/
def psi : (KM F a ≃ₐ[F] KM F a) →* ℂˣ :=
  (Units.map ι.toMonoidHom).comp ((rootsOfUnity 6 F).subtype.comp (kch hζ (rootKF (ℓ := 6) F a)))

variable {F}

theorem psi_apply (σ : KM F a ≃ₐ[F] KM F a) :
    ((psi F hζ ι a σ : ℂˣ) : ℂ) = ι ((kch hζ (rootKF (ℓ := 6) F a) σ : Fˣ) : F) := rfl

theorem psi_injective : Function.Injective (psi F hζ ι a) := by
  intro σ τ h
  apply kch_KF_injective a hζ (rootKF F a) (rootKF_pow F a)
  apply Subtype.ext; apply Units.ext
  apply ι.injective
  have := congrArg (fun x : ℂˣ => (x : ℂ)) h
  simpa [psi_apply] using this

theorem psi_eq_one_iff_forall (σ : KM F a ≃ₐ[F] KM F a) : psi F hζ ι a σ = 1 ↔ σ = 1 :=
  ⟨fun h => psi_injective hζ ι a (h.trans (map_one _).symm), fun h => by rw [h, map_one]⟩

/-- The prime of `𝓞 M` over `v`, as a height-one prime. -/
def wAbove (v : HeightOneSpectrum (𝓞 F)) : HeightOneSpectrum (𝓞 (KM F a)) :=
  ⟨primeAbove F (KM F a) v, (primeAbove_isMaximal F (KM F a) v).isPrime,
    primeAbove_ne_bot F (KM F a) v⟩

theorem wAbove_under (v : HeightOneSpectrum (𝓞 F)) : (wAbove a v).under (𝓞 F) = v := by
  ext1; exact under_primeAbove F (KM F a) v

include hζ in
theorem inertiaGroup_eq_bot (v : HeightOneSpectrum (𝓞 F)) (hv : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (ha : v.valuation F (a : F) = 1) : ArtinL.Abelian.inertiaGroup F (KM F a) v = ⊥ :=
  inertia_eq_bot F hζ v hv a ha (wAbove a v) (wAbove_under a v)

theorem isUnramifiedAt_psi (v : HeightOneSpectrum (𝓞 F)) (hv : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (ha : v.valuation F (a : F) = 1) : ArtinL.Abelian.IsUnramifiedAt (psi F hζ ι a) v := by
  intro σ hσ
  rw [inertiaGroup_eq_bot hζ a v hv ha, Subgroup.mem_bot] at hσ
  rw [hσ, map_one]

include hζ in
/-- **Frobenius.** `kch(Frob_v) = ω` with `ω ≡ a^{(Nv−1)/6} (mod v)` (the argument of C0ZV). -/
theorem kch_artinFrob (v : HeightOneSpectrum (𝓞 F)) (hv : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (ha : v.valuation F (a : F) = 1) (ω : F) (hω : ω ^ 6 = 1)
    (hcong : v.valuation F ((a : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) - ω) < 1) :
    ((kch hζ (rootKF (ℓ := 6) F a) (artinFrob F (KM F a) v) : Fˣ) : F) = ω := by
  classical
  set K := KM F a
  set Q := primeAbove F K v
  let w : HeightOneSpectrum (𝓞 K) := wAbove a v
  have hw : w.under (𝓞 F) = v := wAbove_under a v
  have hQv : Q.under (𝓞 F) = v.asIdeal := under_primeAbove F K v
  set φ := artinFrob F K v
  have hφ : IsArithFrobAt (𝓞 F) φ w.asIdeal := isArithFrobAt_artinFrob F K v
  have hv' : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal := hv
  -- the Kummer value of the Frobenius
  set μ := kch hζ (rootKF F a) φ
  obtain ⟨d, n, β, hd, hn, hnd, hβ, hβpow⟩ := exists_intGen (ℓ := 6) F v a ha
  have hmem : ∀ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) x ∈ w.asIdeal → x ∈ v.asIdeal := by
    intro x hx; rw [← hw]; exact hx
  have hβw : β ∉ w.asIdeal := by
    intro h
    have : β ^ 6 ∈ w.asIdeal := w.asIdeal.pow_mem_of_mem h 6 (Nat.pos_of_ne_zero (NeZero.ne 6))
    rw [hβpow] at this
    rcases v.isPrime.mem_or_mem (hmem _ this) with h3 | h3
    · exact hd (v.isPrime.mem_of_pow_mem _ h3)
    · exact hn h3
  set q := Nat.card (𝓞 F ⧸ v.asIdeal)
  have hq : q = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hFrob : ∀ x : 𝓞 K, φ • x - x ^ q ∈ w.asIdeal := by
    intro x
    have := hφ x
    rw [show w.asIdeal.under (𝓞 F) = v.asIdeal from hQv] at this
    exact this
  -- `6 ∣ q - 1`
  have h6q : 6 ∣ q - 1 := dvd_card_sub_one F hζ v hv
  obtain ⟨K', hK'⟩ := h6q
  have hq1 : q = 6 * K' + 1 := by
    have : 0 < q := by
      rw [hq]; exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
    omega
  have hK'eq : (Ideal.absNorm v.asIdeal - 1) / 6 = K' := by
    rw [← hq, hK', Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne 6))]
  rw [hK'eq] at hcong
  set μO := rootO F μ
  have hsm := smul_intGen F hζ a d β hβ φ
  have hfb := hFrob β
  rw [hsm, hq1, pow_succ, pow_mul, hβpow] at hfb
  have hfb' : algebraMap (𝓞 F) (𝓞 K) (μO - ((d ^ (6 - 1) * n) ^ K')) * β ∈ w.asIdeal := by
    rw [map_sub, map_pow, sub_mul]; convert hfb using 1
  have hμA : μO - (d ^ (6 - 1) * n) ^ K' ∈ v.asIdeal := by
    rcases w.isPrime.mem_or_mem hfb' with h | h
    · exact hmem _ h
    · exact absurd h hβw
  -- valuations in `F`
  set D : F := algebraMap (𝓞 F) F d
  set A : F := algebraMap (𝓞 F) F ((d ^ (6 - 1) * n) ^ K')
  have hDv : v.valuation F D = 1 := (v.valuation_eq_one_iff_notMem (K := F)).mpr hd
  have hA : A = D ^ (q - 1) * (a : F) ^ K' := by
    have h61 : 6 = (6 - 1) + 1 := (Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne 6))).symm
    simp only [A, map_pow, map_mul]
    rw [← hnd, hK']
    have e : D ^ (6 - 1) * ((a : F) * D) = (a : F) * D ^ 6 := by
      conv_rhs => rw [h61, pow_succ]
      ring
    rw [e, mul_pow, ← pow_mul, mul_comm]
  -- Fermat: `D^{q-1} ≡ 1`
  have hferm : v.valuation F (D ^ (q - 1) - 1) < 1 := by
    letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
    have hmd : Ideal.Quotient.mk v.asIdeal d ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have := FiniteField.pow_card_sub_one_eq_one _ hmd
    rw [Fintype.card_eq_nat_card, ← map_pow, ← map_one (Ideal.Quotient.mk v.asIdeal),
      Ideal.Quotient.eq] at this
    have e : D ^ (q - 1) - 1 = algebraMap (𝓞 F) F (d ^ (q - 1) - 1) := by
      simp [D]
    rw [e]
    exact (v.valuation_lt_one_iff_mem (K := F) _).mpr this
  set ωO := toO F ω hω
  have hωF : algebraMap (𝓞 F) F ωO = ω := rfl
  have hωv : v.valuation F ω ≤ 1 := by rw [← hωF]; exact v.valuation_le_one (K := F) ωO
  have hAω : v.valuation F (A - ω) < 1 := by
    rw [hA]
    have e : D ^ (q - 1) * (a : F) ^ K' - ω =
        D ^ (q - 1) * ((a : F) ^ K' - ω) + (D ^ (q - 1) - 1) * ω := by ring
    rw [e]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul, map_pow, hDv, one_pow, one_mul]; exact hcong
    · rw [map_mul]
      calc _ ≤ v.valuation F (D ^ (q - 1) - 1) * 1 := mul_le_mul_right hωv _
        _ < 1 := by rw [mul_one]; exact hferm
  have hμv : v.valuation F (algebraMap (𝓞 F) F μO - A) < 1 := by
    have := (v.valuation_lt_one_iff_mem (K := F) _).mpr hμA
    change v.valuation F (algebraMap (𝓞 F) F (μO - _)) < 1 at this
    rwa [map_sub] at this
  have hμω : μO - ωO ∈ v.asIdeal := by
    rw [← v.valuation_lt_one_iff_mem (K := F)]
    change v.valuation F (algebraMap (𝓞 F) F (μO - ωO)) < 1
    rw [map_sub, hωF]
    have e : algebraMap (𝓞 F) F μO - ω = (algebraMap (𝓞 F) F μO - A) + (A - ω) := by ring
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hμv hAω)
  have heq := eq_of_pow_eq_one_of_sub_mem v.asIdeal hv (rootO_pow F μ) (toO_pow F ω hω) hμω
  have := congrArg (fun x : 𝓞 F => (x : F)) heq
  simpa [μO, rootO, ωO, toO] using this

theorem psi_artinFrob (v : HeightOneSpectrum (𝓞 F)) (hv : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (ha : v.valuation F (a : F) = 1) (ω : F) (hω : ω ^ 6 = 1)
    (hcong : v.valuation F ((a : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) - ω) < 1) :
    ((psi F hζ ι a (artinFrob F (KM F a) v) : ℂˣ) : ℂ) = ι ω := by
  rw [psi_apply, kch_artinFrob hζ a v hv ha ω hω hcong]

/-- **Ramified** at `v` when `6 ∤ v(a)`. -/
theorem not_isUnramifiedAt_psi (v : HeightOneSpectrum (𝓞 F))
    (ha : ∀ k : ℤ, v.valuation F (a : F) ≠ WithZero.exp (6 * k)) :
    ¬ ArtinL.Abelian.IsUnramifiedAt (psi F hζ ι a) v := by
  intro hun
  set K := KM F a
  have hbot : ArtinL.Abelian.inertiaGroup F K v = ⊥ := by
    rw [eq_bot_iff]; intro σ hσ
    rw [Subgroup.mem_bot]; exact (psi_eq_one_iff_forall hζ ι a σ).1 (hun σ hσ)
  have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[F] K) v.asIdeal
    (primeAbove F K v)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal (primeAbove F K v) (K ≃ₐ[F] K)] at h1
  have hc : Nat.card ((primeAbove F K v).inertia (K ≃ₐ[F] K)) = 1 := by
    have : (primeAbove F K v).inertia (K ≃ₐ[F] K) = ⊥ := hbot
    rw [this]; simp
  rw [hc] at h1
  haveI : (wAbove a v).asIdeal.LiesOver v.asIdeal := primeAbove_liesOver F K v
  have he : v.asIdeal.ramificationIdx' (wAbove a v).asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]
    exact h1.symm
  have hval := HeightOneSpectrum.valuation_liesOver K v (wAbove a v) (a : F)
  rw [he, pow_one] at hval
  have hβ : (rootKF (ℓ := 6) F a).β ≠ 0 := (rootKF (ℓ := 6) F a).ne_zero
  have hw0 : (wAbove a v).valuation K (rootKF (ℓ := 6) F a).β ≠ 0 := by
    simpa using hβ
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (wAbove a v).valuation K (rootKF (ℓ := 6) F a).β = WithZero.exp k :=
    ⟨_, (WithZero.exp_log hw0).symm⟩
  apply ha k
  rw [hval, ← rootKF_pow, map_pow, hk, ← WithZero.exp_nsmul]
  congr 1

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_Wild: the conductor exponents of `ψ_a`

* `intValuation_smul_sub_le`: for `σ` in the `i`-th ramification group (`i ≥ 1`), i.e.
  `σ x ≡ x (mod 𝔓^{i+1})` for all `x`, one has `w(σx − x) ≤ w(x) e^{−i}` (uniformizer induction).
* `le_of_mem_ramificationGroup`: if moreover `ψ_a σ ≠ 1` then `i ≤ 6 n_v`, where `v(6) = e^{−n_v}`.
* `conductorExponent_psi_le`: `e_v(ψ_a) ≤ 1 + 6 n_v`; it is `0` where `ψ_a` is unramified and `≤ 1`
  at `v ∤ 6`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin ArtinPrimitiveRoots.L3K.KB WithZero

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

section Generic

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {G : Type*} [Group G]
  [MulSemiringAction G R] (w : HeightOneSpectrum R)

/-- A factorization `t x = ϖ x'` with `t ∉ 𝔓`, for `x ∈ 𝔓` and `w(ϖ) = e^{−1}`. -/
lemma exists_mul_eq_mul (ϖ x : R) (hϖ : w.intValuation ϖ = exp (-1 : ℤ)) (hx : x ∈ w.asIdeal) :
    ∃ t x' : R, t ∉ w.asIdeal ∧ t * x = ϖ * x' := by
  have hϖmem : ϖ ∈ w.asIdeal := by
    rw [← w.intValuation_lt_one_iff_mem, hϖ]; rw [← exp_zero]; exact exp_lt_exp.2 (by norm_num)
  obtain ⟨B, hB⟩ : w.asIdeal ∣ Ideal.span {ϖ} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hϖmem
  have hBnot : ¬ B ≤ w.asIdeal := by
    intro hle
    have : Ideal.span {ϖ} ≤ w.asIdeal ^ 2 := by
      rw [hB, sq]; exact Ideal.mul_mono_right hle
    rw [Ideal.span_singleton_le_iff_mem, ← w.intValuation_le_pow_iff_mem, hϖ] at this
    have := exp_le_exp.1 this
    norm_num at this
  obtain ⟨t, htB, htw⟩ := SetLike.not_le_iff_exists.1 hBnot
  have hmem : t * x ∈ Ideal.span {ϖ} := by
    rw [hB, mul_comm w.asIdeal B]; exact Ideal.mul_mem_mul htB hx
  obtain ⟨x', hx'⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨t, x', htw, by rw [← hx', mul_comm]⟩

/-- **Relative congruence.** -/
theorem intValuation_smul_sub_le (σ : G) (i : ℕ) (hi : 1 ≤ i)
    (hσ : ∀ x : R, σ • x - x ∈ w.asIdeal ^ (i + 1)) :
    ∀ m : ℕ, ∀ x : R, w.intValuation x = exp (-(m : ℤ)) →
      w.intValuation (σ • x - x) ≤ exp (-((m + i : ℕ) : ℤ)) := by
  have hbase : ∀ x : R, w.intValuation (σ • x - x) ≤ exp (-((i + 1 : ℕ) : ℤ)) := fun x =>
    (w.intValuation_le_pow_iff_mem _ _).2 (hσ x)
  obtain ⟨ϖ, hϖ⟩ := w.intValuation_exists_uniformizer
  intro m
  induction m with
  | zero =>
    intro x _
    refine (hbase x).trans (exp_le_exp.2 ?_)
    push_cast; linarith
  | succ m ih =>
    intro x hx
    have hxmem : x ∈ w.asIdeal := by
      rw [← w.intValuation_lt_one_iff_mem, hx]; rw [← exp_zero]; exact exp_lt_exp.2 (by push_cast; linarith)
    obtain ⟨t, x', ht, htx⟩ := exists_mul_eq_mul w ϖ x hϖ hxmem
    have hvt : w.intValuation t = 1 := HeightOneSpectrum.intValuation_eq_one_iff.2 ht
    have hvx' : w.intValuation x' = exp (-(m : ℤ)) := by
      have h1 := congrArg w.intValuation htx
      rw [map_mul, map_mul, hvt, one_mul, hx, hϖ] at h1
      have h2 : exp (-((m + 1 : ℕ) : ℤ)) = exp (-1 : ℤ) * exp (-(m : ℤ)) := by
        rw [← exp_add]; congr 1; push_cast; ring
      rw [h2] at h1
      exact (mul_left_cancel₀ (by simp) h1).symm
    have ih' := ih x' hvx'
    -- `w(σ x') ≤ e^{−m}`
    have hσx' : w.intValuation (σ • x') ≤ exp (-(m : ℤ)) := by
      have : σ • x' = x' + (σ • x' - x') := by ring
      rw [this]
      refine (Valuation.map_add _ _ _).trans (max_le hvx'.le (ih'.trans (exp_le_exp.2 ?_)))
      push_cast; linarith
    -- `w(σ(t x) − t x) ≤ e^{−(m+1+i)}`
    have hϖσ := hbase ϖ
    have h1 : σ • (t * x) - t * x = (σ • ϖ - ϖ) * σ • x' + ϖ * (σ • x' - x') := by
      rw [htx, smul_mul']; ring
    have hA : w.intValuation (σ • (t * x) - t * x) ≤ exp (-((m + 1 + i : ℕ) : ℤ)) := by
      rw [h1]
      refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
      · rw [map_mul]
        calc w.intValuation (σ • ϖ - ϖ) * w.intValuation (σ • x')
            ≤ exp (-((i + 1 : ℕ) : ℤ)) * exp (-(m : ℤ)) := mul_le_mul' hϖσ hσx'
          _ = exp (-((m + 1 + i : ℕ) : ℤ)) := by rw [← exp_add]; congr 1; push_cast; ring
      · rw [map_mul, hϖ]
        calc exp (-1 : ℤ) * w.intValuation (σ • x' - x')
            ≤ exp (-1 : ℤ) * exp (-((m + i : ℕ) : ℤ)) := mul_le_mul_right ih' _
          _ = exp (-((m + 1 + i : ℕ) : ℤ)) := by rw [← exp_add]; congr 1; push_cast; ring
    -- `w(σ t) = 1`
    have hσt : w.intValuation (σ • t) = 1 := by
      have hlt : w.intValuation (σ • t - t) < 1 :=
        (hbase t).trans_lt (by rw [← exp_zero]; exact exp_lt_exp.2 (by push_cast; linarith))
      have : σ • t = t + (σ • t - t) := by ring
      rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [hvt]; exact hlt), hvt]
    have h2 : σ • (t * x) - t * x = σ • t * (σ • x - x) + x * (σ • t - t) := by
      rw [smul_mul']; ring
    have hB : w.intValuation (x * (σ • t - t)) ≤ exp (-((m + 1 + i : ℕ) : ℤ)) := by
      rw [map_mul, hx]
      calc exp (-((m + 1 : ℕ) : ℤ)) * w.intValuation (σ • t - t)
          ≤ exp (-((m + 1 : ℕ) : ℤ)) * exp (-((i + 1 : ℕ) : ℤ)) := mul_le_mul_right (hbase t) _
        _ ≤ exp (-((m + 1 + i : ℕ) : ℤ)) := by
          rw [← exp_add]; exact exp_le_exp.2 (by push_cast; linarith)
    have hC : w.intValuation (σ • t * (σ • x - x)) ≤ exp (-((m + 1 + i : ℕ) : ℤ)) := by
      have : σ • t * (σ • x - x) = (σ • (t * x) - t * x) - x * (σ • t - t) := by rw [h2]; ring
      rw [this]
      refine (Valuation.map_sub _ _ _).trans (max_le hA hB)
    rw [map_mul, hσt, one_mul] at hC
    convert hC using 3

end Generic

section Kummer

variable {F : Type} [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 6) (ι : F →+* ℂ)
  (a : Fˣ)

/-- `6 = (1 − μ) c` in `𝓞 F` for a sixth root of unity `μ ≠ 1`. -/
lemma six_eq_mul {R : Type*} [CommRing R] [IsDomain R] {μ : R} (h6 : μ ^ 6 = 1) (h1 : μ ≠ 1) :
    ∃ c : R, (6 : R) = (1 - μ) * c := by
  have hsum : ∑ k ∈ Finset.range 6, μ ^ k = 0 := by
    have h := geom_sum_mul μ 6
    rw [h6, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 h1)
  refine ⟨∑ k ∈ Finset.range 6, ∑ j ∈ Finset.range k, μ ^ j, ?_⟩
  have : ∑ k ∈ Finset.range 6, (∑ j ∈ Finset.range k, μ ^ j) * (μ - 1) =
      ∑ k ∈ Finset.range 6, (μ ^ k - 1) := Finset.sum_congr rfl fun k _ => geom_sum_mul μ k
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, hsum] at this
  simp at this
  linear_combination this

/-- An integral Kummer generator `y = d β`. -/
lemma exists_intGen' : ∃ (d : 𝓞 F) (y : 𝓞 (KM F a)), d ≠ 0 ∧
    (y : KM F a) = algebraMap F (KM F a) (algebraMap (𝓞 F) F d) * (rootKF (ℓ := 6) F a).β := by
  obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (a : F)
  have hd0 : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.ne_zero hd
  set K := KM F a
  set β : K := algebraMap F K (algebraMap (𝓞 F) F d) * (rootKF (ℓ := 6) F a).β
  have hdF : algebraMap (𝓞 F) F d ≠ 0 := by simpa using hd0
  have hβpow : β ^ 6 = algebraMap F K (algebraMap (𝓞 F) F (d ^ 5 * n)) := by
    rw [mul_pow, rootKF_pow, ← map_pow, ← map_mul]
    congr 1
    rw [← hnd, map_mul, map_pow]
    field_simp
  have hint : IsIntegral ℤ β := by
    apply IsIntegral.of_pow (by norm_num : 0 < 6)
    rw [hβpow, ← IsScalarTower.algebraMap_apply]
    exact (((d : 𝓞 F) ^ 5 * n).isIntegral_coe).map (IsScalarTower.toAlgHom ℤ F K)
  exact ⟨d, ⟨β, hint⟩, hd0, rfl⟩

/-- `v(6) = e^{−n_v}`. -/
def n6 (v : HeightOneSpectrum (𝓞 F)) : ℕ := (-(log (v.intValuation (6 : 𝓞 F)))).toNat

lemma intValuation_six (v : HeightOneSpectrum (𝓞 F)) :
    v.intValuation (6 : 𝓞 F) = exp (-((n6 v : ℕ) : ℤ)) := by
  have h6 : (6 : 𝓞 F) ≠ 0 := by
    intro h; have := congrArg (fun x : 𝓞 F => (x : F)) h; simp at this
  have hne := v.intValuation_ne_zero _ h6
  have hle := v.intValuation_le_one (6 : 𝓞 F)
  have hlog : log (v.intValuation (6 : 𝓞 F)) ≤ 0 := by
    rw [← exp_log hne, ← exp_zero, exp_le_exp] at hle; exact hle
  rw [n6, Int.toNat_of_nonneg (by linarith), neg_neg, exp_log hne]

lemma n6_eq_zero (v : HeightOneSpectrum (𝓞 F)) (hv : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal) : n6 v = 0 := by
  have h1 : v.intValuation (6 : 𝓞 F) = 1 := HeightOneSpectrum.intValuation_eq_one_iff.2 (by
    simpa using hv)
  have := intValuation_six v
  rw [h1] at this
  have h2 := congrArg log this
  rw [log_one, log_exp] at h2
  omega

include hζ in
lemma card_gal_le : Nat.card (KM F a ≃ₐ[F] KM F a) ≤ 6 :=
  (Nat.card_le_card_of_injective _ (kch_KF_injective a hζ (rootKF F a) (rootKF_pow F a))).trans
    (card_rootsOfUnity _ _)

include hζ in
/-- **Wild bound.** If `σ` lies in the `i`-th ramification group (`i ≥ 1`) and `ψ_a σ ≠ 1`,
then `i ≤ 6 n_v`. -/
theorem le_of_mem_ramificationGroup (v : HeightOneSpectrum (𝓞 F)) (i : ℕ) (hi : 1 ≤ i)
    (σ : KM F a ≃ₐ[F] KM F a) (hσ : σ ∈ ArtinL.Abelian.ramificationGroup F (KM F a) v i)
    (hψ : psi F hζ ι a σ ≠ 1) : i ≤ 6 * n6 v := by
  set K := KM F a
  set w := wAbove a v
  haveI : w.asIdeal.LiesOver v.asIdeal := primeAbove_liesOver F K v
  obtain ⟨d, y, hd, hy⟩ := exists_intGen' a
  set μ := rootO F (kch hζ (rootKF (ℓ := 6) F a) σ)
  have hsm : σ • y = algebraMap (𝓞 F) (𝓞 K) μ * y := smul_intGen F hζ a d y hy σ
  have hμ1 : μ ≠ 1 := by
    intro h
    apply hψ
    have : kch hζ (rootKF (ℓ := 6) F a) σ = 1 := by
      apply Subtype.ext; apply Units.ext
      have := congrArg (fun x : 𝓞 F => (x : F)) h
      simpa [μ, rootO] using this
    rw [psi, MonoidHom.comp_apply, MonoidHom.comp_apply, this]; simp
  have hy0 : y ≠ 0 := by
    intro h
    have : (y : K) = 0 := by rw [h]; rfl
    rw [hy] at this
    simp at this
    rcases this with h1 | h1
    · exact hd h1
    · exact (rootKF (ℓ := 6) F a).ne_zero h1
  set m : ℕ := (-(log (w.intValuation y))).toNat
  have hwy : w.intValuation y = exp (-(m : ℤ)) := by
    have hne := w.intValuation_ne_zero _ hy0
    have hlog : log (w.intValuation y) ≤ 0 := by
      have hle := w.intValuation_le_one y
      rw [← exp_log hne, ← exp_zero, exp_le_exp] at hle; exact hle
    rw [Int.toNat_of_nonneg (by linarith), neg_neg, exp_log hne]
  have hin : ∀ x : 𝓞 K, σ • x - x ∈ w.asIdeal ^ (i + 1) := fun x => hσ x
  have hrel := intValuation_smul_sub_le w σ i hi hin m y hwy
  rw [hsm, show algebraMap (𝓞 F) (𝓞 K) μ * y - y = algebraMap (𝓞 F) (𝓞 K) (μ - 1) * y by
    rw [map_sub, map_one]; ring, map_mul, hwy] at hrel
  have hμv : w.intValuation (algebraMap (𝓞 F) (𝓞 K) (μ - 1)) ≤ exp (-(i : ℤ)) := by
    have h2 : exp (-((m + i : ℕ) : ℤ)) = exp (-(i : ℤ)) * exp (-(m : ℤ)) := by
      rw [← exp_add]; congr 1; push_cast; ring
    rw [h2] at hrel
    exact le_of_mul_le_mul_right hrel (by simp)
  obtain ⟨c, hc⟩ := six_eq_mul (rootO_pow F _) hμ1
  have h6 : w.intValuation (algebraMap (𝓞 F) (𝓞 K) 6) ≤ exp (-(i : ℤ)) := by
    rw [hc, map_mul, map_mul]
    have hneg : w.intValuation (algebraMap (𝓞 F) (𝓞 K) (1 - μ)) =
        w.intValuation (algebraMap (𝓞 F) (𝓞 K) (μ - 1)) := by
      rw [show (1 : 𝓞 F) - μ = -(μ - 1) by ring, map_neg, Valuation.map_neg]
    rw [hneg]
    calc _ ≤ w.intValuation (algebraMap (𝓞 F) (𝓞 K) (μ - 1)) * 1 :=
          mul_le_mul_right (w.intValuation_le_one _) _
      _ ≤ exp (-(i : ℤ)) := by rw [mul_one]; exact hμv
  rw [← HeightOneSpectrum.intValuation_liesOver v w, intValuation_six, ← exp_nsmul] at h6
  rw [exp_le_exp] at h6
  -- `e ≤ 6`
  have he : v.asIdeal.ramificationIdx' w.asIdeal ≤ 6 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]
    have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[F] K) v.asIdeal
      (primeAbove F K v)
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal (primeAbove F K v) (K ≃ₐ[F] K)] at h1
    change (primeAbove F K v).ramificationIdx (𝓞 F) ≤ 6
    rw [← h1]
    exact (Subgroup.card_le_card_group _).trans (card_gal_le hζ a)
  have : (i : ℤ) ≤ (v.asIdeal.ramificationIdx' w.asIdeal) * (n6 v) := by
    simp only [nsmul_eq_mul] at h6; push_cast at h6; linarith
  have h3 : ((v.asIdeal.ramificationIdx' w.asIdeal : ℕ) : ℤ) * (n6 v) ≤ 6 * (n6 v) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast he) (by positivity)
  omega

lemma ramificationGroup_le_inertiaGroup (v : HeightOneSpectrum (𝓞 F)) (i : ℕ) :
    ArtinL.Abelian.ramificationGroup F (KM F a) v i ≤ ArtinL.Abelian.inertiaGroup F (KM F a) v := by
  intro σ hσ x
  exact Ideal.pow_le_self (Nat.succ_ne_zero i) (hσ x)

/-- The swan conductor is at most `6 n_v`, and `0` if `ψ_a` is trivial on the higher groups. -/
theorem swanConductor_psi_le (v : HeightOneSpectrum (𝓞 F)) (B : ℕ)
    (hB : ∀ i : ℕ, 1 ≤ i → ∀ σ ∈ ArtinL.Abelian.ramificationGroup F (KM F a) v i,
      psi F hζ ι a σ ≠ 1 → i ≤ B) :
    ArtinL.Abelian.swanConductor (psi F hζ ι a) v ≤ B := by
  classical
  unfold ArtinL.Abelian.swanConductor
  set f : ℕ → ℚ := fun i =>
    (Nat.card (ArtinL.Abelian.ramificationGroup F (KM F a) v (i + 1)) : ℚ) /
      (Nat.card (ArtinL.Abelian.inertiaGroup F (KM F a) v) : ℚ) *
      (if ∀ σ ∈ ArtinL.Abelian.ramificationGroup F (KM F a) v (i + 1), psi F hζ ι a σ = 1
        then 0 else 1)
  have hsupp : Function.support f ⊆ (Finset.range B : Set ℕ) := by
    intro i hi
    rw [Function.mem_support] at hi
    by_contra hiB
    apply hi
    simp only [f]
    rw [if_pos, mul_zero]
    intro σ hσ
    by_contra hne
    have := hB (i + 1) (by omega) σ hσ hne
    simp at hiB; omega
  rw [finsum_eq_sum_of_support_subset f hsupp]
  have hle : ∀ i ∈ Finset.range B, f i ≤ 1 := by
    intro i _
    simp only [f]
    have hpos : (0 : ℚ) < Nat.card (ArtinL.Abelian.inertiaGroup F (KM F a) v) := by
      exact_mod_cast Nat.card_pos
    have hcard : (Nat.card (ArtinL.Abelian.ramificationGroup F (KM F a) v (i + 1)) : ℚ) ≤
        Nat.card (ArtinL.Abelian.inertiaGroup F (KM F a) v) := by
      exact_mod_cast Subgroup.card_le_of_le (ramificationGroup_le_inertiaGroup a v (i + 1))
    have h1 : (Nat.card (ArtinL.Abelian.ramificationGroup F (KM F a) v (i + 1)) : ℚ) /
        (Nat.card (ArtinL.Abelian.inertiaGroup F (KM F a) v) : ℚ) ≤ 1 :=
      (div_le_one hpos).2 hcard
    have h0 : (0 : ℚ) ≤ (Nat.card (ArtinL.Abelian.ramificationGroup F (KM F a) v (i + 1)) : ℚ) /
        (Nat.card (ArtinL.Abelian.inertiaGroup F (KM F a) v) : ℚ) := by positivity
    split_ifs <;> nlinarith
  calc ∑ i ∈ Finset.range B, f i ≤ ∑ _i ∈ Finset.range B, (1 : ℚ) := Finset.sum_le_sum hle
    _ = B := by simp

theorem swanConductor_psi_le_six (v : HeightOneSpectrum (𝓞 F)) :
    ArtinL.Abelian.swanConductor (psi F hζ ι a) v ≤ (6 * n6 v : ℕ) :=
  swanConductor_psi_le hζ ι a v _ fun i hi σ hσ hψ => le_of_mem_ramificationGroup hζ ι a v i hi σ hσ hψ

/-- `e_v(ψ_a) ≤ 1 + 6 n_v`. -/
theorem conductorExponent_psi_le (v : HeightOneSpectrum (𝓞 F)) :
    ArtinL.Abelian.conductorExponent (psi F hζ ι a) v ≤ 1 + 6 * n6 v := by
  unfold ArtinL.Abelian.conductorExponent
  have h1 : ⌈ArtinL.Abelian.swanConductor (psi F hζ ι a) v⌉₊ ≤ 6 * n6 v := by
    rw [Nat.ceil_le]; exact_mod_cast swanConductor_psi_le_six hζ ι a v
  split_ifs <;> omega

/-- `e_v(ψ_a) ≤ 1` at `v ∤ 6`. -/
theorem conductorExponent_psi_le_one (v : HeightOneSpectrum (𝓞 F))
    (hv : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    ArtinL.Abelian.conductorExponent (psi F hζ ι a) v ≤ 1 := by
  have := conductorExponent_psi_le hζ ι a v
  rw [n6_eq_zero v hv] at this; simpa using this

/-- `e_v(ψ_a) = 0` where `ψ_a` is unramified. -/
theorem conductorExponent_psi_eq_zero (v : HeightOneSpectrum (𝓞 F))
    (hun : ArtinL.Abelian.IsUnramifiedAt (psi F hζ ι a) v) :
    ArtinL.Abelian.conductorExponent (psi F hζ ι a) v = 0 := by
  have hs : ArtinL.Abelian.swanConductor (psi F hζ ι a) v ≤ (0 : ℕ) :=
    swanConductor_psi_le hζ ι a v 0 fun i _ σ hσ hψ =>
      absurd (hun σ (ramificationGroup_le_inertiaGroup a v i hσ)) hψ
  unfold ArtinL.Abelian.conductorExponent
  rw [if_pos hun, zero_add, Nat.ceil_eq_zero]
  exact_mod_cast hs

end Kummer

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_Cond: `N 𝔣(ψ_a) ≤ N(D₆) · N(𝔟)`

`D₆ = ∏_{v ∣ 6} v^{1 + 6 n_v}` depends on `F` only; `𝔟` is any nonzero ideal contained in every
`v ∤ 6` at which `a` is not a unit. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin ArtinPrimitiveRoots.L3K.KB WithZero

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

section Gen

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

lemma mulSupport_pow_subset (f : HeightOneSpectrum R → ℕ) :
    Function.mulSupport (fun v : HeightOneSpectrum R => v.asIdeal ^ f v) ⊆ {v | f v ≠ 0} := by
  intro v hv
  simp only [Function.mem_mulSupport] at hv
  intro h0; apply hv; rw [h0, pow_zero]

lemma finprod_pow_dvd {e f : HeightOneSpectrum R → ℕ} (hf : {v | f v ≠ 0}.Finite)
    (h : ∀ v, e v ≤ f v) :
    ∏ᶠ v, v.asIdeal ^ e v ∣ ∏ᶠ v, v.asIdeal ^ f v := by
  have he : {v | e v ≠ 0} ⊆ {v | f v ≠ 0} := fun v hv => by
    simp only [Set.mem_ofPred_eq] at hv ⊢; have := h v; omega
  rw [finprod_eq_prod_of_mulSupport_subset _ ((mulSupport_pow_subset e).trans
      (he.trans hf.coe_toFinset.symm.subset)),
    finprod_eq_prod_of_mulSupport_subset _ ((mulSupport_pow_subset f).trans
      hf.coe_toFinset.symm.subset)]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun v _ => pow_dvd_pow _ (h v)

lemma finprod_pow_add {f g : HeightOneSpectrum R → ℕ} (hf : {v | f v ≠ 0}.Finite)
    (hg : {v | g v ≠ 0}.Finite) :
    ∏ᶠ v, v.asIdeal ^ (f v + g v) = (∏ᶠ v, v.asIdeal ^ f v) * ∏ᶠ v, v.asIdeal ^ g v := by
  simp_rw [pow_add]
  exact finprod_mul_distrib ((hf.subset (mulSupport_pow_subset f)))
    ((hg.subset (mulSupport_pow_subset g)))

lemma finprod_count_eq {I : Ideal R} (hI : I ≠ ⊥) :
    ∏ᶠ v : HeightOneSpectrum R,
      v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors = I :=
  Ideal.finprod_heightOneSpectrum_factorization hI

lemma finite_count {I : Ideal R} (hI : I ≠ ⊥) :
    {v : HeightOneSpectrum R | (Associates.mk v.asIdeal).count (Associates.mk I).factors ≠ 0}.Finite := by
  have := Ideal.hasFiniteMulSupport (R := R) hI
  refine this.subset fun v hv => ?_
  simp only [Set.mem_ofPred_eq] at hv
  simp only [Function.mem_mulSupport, HeightOneSpectrum.maxPowDividing]
  intro h1
  have : v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors ≤ v.asIdeal ^ 1 := by
    exact Ideal.pow_le_pow_right (Nat.one_le_iff_ne_zero.2 hv)
  rw [h1, pow_one, Ideal.one_eq_top, top_le_iff] at this
  exact v.isPrime.ne_top this

lemma one_le_count {I : Ideal R} (hI : I ≠ ⊥) (v : HeightOneSpectrum R) (hv : I ≤ v.asIdeal) :
    1 ≤ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
  rw [Nat.one_le_iff_ne_zero]
  exact (Associates.count_ne_zero_iff_dvd hI v.irreducible).2 (Ideal.dvd_iff_le.2 hv)

end Gen

variable {F : Type} [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 6) (ι : F →+* ℂ)
  (a : Fˣ)

open scoped Classical in
/-- The wild exponents. -/
def a6 (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  if ((6 : ℕ) : 𝓞 F) ∈ v.asIdeal then 1 + 6 * n6 v else 0

/-- `D₆ = ∏_{v ∣ 6} v^{1 + 6 n_v}`. -/
def D6 (F : Type) [Field F] [NumberField F] : Ideal (𝓞 F) := ∏ᶠ v, v.asIdeal ^ a6 v

lemma finite_a6 : {v : HeightOneSpectrum (𝓞 F) | a6 v ≠ 0}.Finite := by
  classical
  have h6 : (Ideal.span {((6 : ℕ) : 𝓞 F)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    intro h; have := congrArg (fun x : 𝓞 F => (x : F)) h; simp at this
  refine (finite_count h6).subset fun v hv => ?_
  simp only [Set.mem_ofPred_eq, a6] at hv ⊢
  split_ifs at hv with h
  · have := one_le_count h6 v (by rw [Ideal.span_singleton_le_iff_mem]; exact h); omega
  · exact absurd rfl hv

theorem absNorm_conductor_psi_le (𝔟 : Ideal (𝓞 F)) (h𝔟 : 𝔟 ≠ ⊥)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal →
      v.valuation F (a : F) ≠ 1 → 𝔟 ≤ v.asIdeal) :
    Ideal.absNorm (ArtinL.Abelian.conductor (psi F hζ ι a)) ≤
      Ideal.absNorm (D6 F) * Ideal.absNorm 𝔟 := by
  classical
  have hdvd : ArtinL.Abelian.conductor (psi F hζ ι a) ∣ D6 F * 𝔟 := by
    rw [D6, ← finprod_count_eq h𝔟, ← finprod_pow_add finite_a6 (finite_count h𝔟),
      ArtinL.Abelian.conductor]
    refine finprod_pow_dvd (finite_a6.union (finite_count h𝔟) |>.subset fun v hv => by
      simp only [Set.mem_ofPred_eq, Set.mem_union] at hv ⊢; omega) fun v => ?_
    by_cases h6 : ((6 : ℕ) : 𝓞 F) ∈ v.asIdeal
    · have := conductorExponent_psi_le hζ ι a v
      simp only [a6, if_pos h6]; omega
    · by_cases hv : v.valuation F (a : F) = 1
      · rw [conductorExponent_psi_eq_zero hζ ι a v (isUnramifiedAt_psi hζ ι a v h6 hv)]
        omega
      · have h1 := conductorExponent_psi_le_one hζ ι a v h6
        have h2 := one_le_count h𝔟 v (h v h6 hv)
        omega
  have hne : D6 F * 𝔟 ≠ ⊥ := by
    refine mul_ne_zero ?_ h𝔟
    rw [D6, finprod_eq_prod_of_mulSupport_subset _ ((mulSupport_pow_subset _).trans
      finite_a6.coe_toFinset.symm.subset)]
    exact Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ v.ne_bot
  have := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd)
  rw [map_mul] at this
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (by
    rw [← map_mul, Ne, Ideal.absNorm_eq_zero_iff]; exact hne)) this

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_Val: valuations of a generator `u` of `𝔲 R` at exterior primes

For `u ∈ R = SInt 𝔪` with `u R = 𝔲 R` and an exterior prime `v`: `v(u) = e^{−e}` where
`𝔲 ≤ v^e`, `𝔲 ≰ v^{e+1}`. Hence `v(u) = 1` if `v ∤ 𝔲`, and `v(u)` is not an even sixth power of
`e^{±1}` when `v ∣ 𝔲` and `𝔲` is sixth-power-free. -/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots WithZero

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

lemma sInt_val_le_one' (s : SInt 𝔪) (w : HeightOneSpectrum (𝓞 F)) (hw : ¬ 𝔪 ≤ w.asIdeal) :
    w.valuation F (s : F) ≤ 1 :=
  s.2 w hw

lemma coe_algebraMap_sInt' (a : 𝓞 F) :
    ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) = algebraMap (𝓞 F) F a := rfl

lemma val_algebraMap_le (v : HeightOneSpectrum (𝓞 F)) {x : 𝓞 F} {e : ℕ} (hx : x ∈ v.asIdeal ^ e) :
    v.valuation F (algebraMap (𝓞 F) F x) ≤ exp (-(e : ℤ)) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (v.intValuation_le_pow_iff_mem x e).2 hx

lemma val_le_of_le (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) {𝔲 : Ideal (𝓞 F)}
    {u : SInt 𝔪} (hu : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪))) {e : ℕ}
    (he : 𝔲 ≤ v.asIdeal ^ e) : v.valuation F (u : F) ≤ exp (-(e : ℤ)) := by
  have hmem : u ∈ 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hu]; exact Ideal.mem_span_singleton_self u
  clear hu
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    rw [coe_algebraMap_sInt']
    exact val_algebraMap_le v (he hy)
  | zero => simp
  | add x y _ _ hx hy =>
    have : ((x + y : SInt 𝔪) : F) = (x : F) + (y : F) := rfl
    rw [this]; exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | smul r x _ hx =>
    have : ((r • x : SInt 𝔪) : F) = (r : F) * (x : F) := rfl
    rw [this, map_mul]
    calc v.valuation F (r : F) * v.valuation F (x : F) ≤ 1 * exp (-(e : ℤ)) :=
          mul_le_mul' (sInt_val_le_one' r v hv) hx
      _ = _ := one_mul _

lemma lt_val_of_not_le (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) {𝔲 : Ideal (𝓞 F)}
    {u : SInt 𝔪} (hu : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪))) {n : ℕ}
    (hn : ¬ 𝔲 ≤ v.asIdeal ^ n) : exp (-(n : ℤ)) < v.valuation F (u : F) := by
  obtain ⟨x, hx𝔲, hxn⟩ := SetLike.not_le_iff_exists.1 hn
  have hx : algebraMap (𝓞 F) (SInt 𝔪) x ∈ Ideal.span {u} := by
    rw [hu]; exact Ideal.mem_map_of_mem _ hx𝔲
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hx
  have h1 : exp (-(n : ℤ)) < v.valuation F (algebraMap (𝓞 F) F x) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    by_contra h; push Not at h
    exact hxn ((v.intValuation_le_pow_iff_mem x n).1 h)
  have h2 : algebraMap (𝓞 F) F x = (r : F) * (u : F) := by
    rw [← coe_algebraMap_sInt', ← hr]; rfl
  rw [h2, map_mul] at h1
  calc exp (-(n : ℤ)) < v.valuation F (r : F) * v.valuation F (u : F) := h1
    _ ≤ 1 * v.valuation F (u : F) := mul_le_mul' (sInt_val_le_one' r v hv) le_rfl
    _ = _ := one_mul _

/-- `v(u) = e^{−e}` when `𝔲 ≤ v^e` and `𝔲 ≰ v^{e+1}`. -/
lemma val_eq_exp (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) {𝔲 : Ideal (𝓞 F)}
    {u : SInt 𝔪} (hu : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪))) {e : ℕ}
    (he : 𝔲 ≤ v.asIdeal ^ e) (he1 : ¬ 𝔲 ≤ v.asIdeal ^ (e + 1)) :
    v.valuation F (u : F) = exp (-(e : ℤ)) := by
  have hle := val_le_of_le v hv hu he
  have hlt := lt_val_of_not_le v hv hu he1
  have hne : v.valuation F (u : F) ≠ 0 := ne_of_gt ((zero_lt_iff.2 (exp_ne_zero)).trans hlt)
  rw [← exp_log hne] at hle hlt ⊢
  rw [exp_le_exp] at hle
  rw [exp_lt_exp] at hlt
  congr 1
  push_cast at hlt
  omega

lemma val_eq_one (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) {𝔲 : Ideal (𝓞 F)}
    {u : SInt 𝔪} (hu : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (h : ¬ 𝔲 ≤ v.asIdeal) : v.valuation F (u : F) = 1 := by
  have := val_eq_exp v hv hu (e := 0) (by simp) (by simpa using h)
  simpa using this

/-- At a prime dividing a sixth-power-free `𝔲`, `v(u)` is not `e^{6k}`. -/
lemma val_ne_exp_six (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) {𝔲 : Ideal (𝓞 F)}
    (h6 : IsSixthPowerFree 𝔲) {u : SInt 𝔪}
    (hu : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪))) (h : 𝔲 ≤ v.asIdeal) :
    ∀ k : ℤ, v.valuation F (u : F) ≠ exp (6 * k) := by
  classical
  have hex : ∃ n, ¬ 𝔲 ≤ v.asIdeal ^ n := by
    refine ⟨6, fun hle => ?_⟩
    have := h6 v.asIdeal (Ideal.dvd_iff_le.2 hle)
    exact v.isPrime.ne_top (Ideal.isUnit_iff.1 this)
  set n₀ := Nat.find hex
  have hn₀ : ¬ 𝔲 ≤ v.asIdeal ^ n₀ := Nat.find_spec hex
  have hn₀6 : n₀ ≤ 6 := Nat.find_min' hex (fun hle => by
    have := h6 v.asIdeal (Ideal.dvd_iff_le.2 hle)
    exact v.isPrime.ne_top (Ideal.isUnit_iff.1 this))
  have hn₀2 : 2 ≤ n₀ := by
    by_contra hlt; push Not at hlt
    interval_cases hn : n₀
    · exact hn₀ (by simp)
    · exact hn₀ (by simpa using h)
  have he : 𝔲 ≤ v.asIdeal ^ (n₀ - 1) := by
    by_contra hc
    exact Nat.find_min hex (by omega : n₀ - 1 < n₀) hc
  have hval := val_eq_exp v hv hu he (by rwa [Nat.sub_add_cancel (by omega)])
  intro k hk
  rw [hval, exp_inj] at hk
  omega

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-!
# Transport of `AllowedGen` along a field isomorphism

Used to move from `F : Type u` to the universe-0 copy `CyclotomicField n ℚ`.
-/

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain

namespace C0R

/-! ### Generic facts on ideals along a ring equivalence -/

section Ideals

variable {R S : Type*} [CommRing R] [CommRing S]

theorem mem_map_equiv (f : R ≃+* S) (I : Ideal R) (y : S) : y ∈ I.map f ↔ f.symm y ∈ I := by
  rw [Ideal.mem_map_of_equiv]
  exact ⟨fun ⟨x, hx, hxy⟩ => by rw [← hxy, f.symm_apply_apply]; exact hx,
    fun h => ⟨_, h, f.apply_symm_apply y⟩⟩

theorem map_equiv_le_iff (f : R ≃+* S) {I J : Ideal R} : I.map f ≤ J.map f ↔ I ≤ J := by
  constructor
  · intro h x hx
    have : f x ∈ J.map f := h ((mem_map_equiv f I _).2 (by simpa using hx))
    simpa using (mem_map_equiv f J _).1 this
  · intro h y hy
    exact (mem_map_equiv f J y).2 (h ((mem_map_equiv f I y).1 hy))

theorem map_equiv_symm_map (f : R ≃+* S) (I : Ideal R) : (I.map f).map f.symm = I := by
  ext x
  rw [mem_map_equiv, RingEquiv.symm_symm, mem_map_equiv, RingEquiv.symm_apply_apply]

theorem map_equiv_coe (f : R ≃+* S) (I : Ideal R) : I.map (f : R →+* S) = I.map f := rfl

end Ideals

/-! ### The equivalences -/

variable {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']

omit [NumberField F] [NumberField F'] in
theorem mapRingEquiv_symm (e : F ≃+* F') :
    RingOfIntegers.mapRingEquiv e.symm = (RingOfIntegers.mapRingEquiv e).symm := by
  ext x; rfl

/-- `S`-integrality transports along `e`. -/
theorem mem_integer_map (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) (x : F)
    (hx : x ∈ (placesOf 𝔪).integer F) :
    e x ∈ (placesOf (𝔪.map (RingOfIntegers.mapRingEquiv e))).integer F' := by
  set eO := RingOfIntegers.mapRingEquiv e
  intro v' hv'
  let v : HeightOneSpectrum (𝓞 F) :=
    { asIdeal := v'.asIdeal.comap (eO : 𝓞 F →+* 𝓞 F')
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := by
        intro h
        apply v'.ne_bot
        rw [← Ideal.map_comap_of_surjective (eO : 𝓞 F →+* 𝓞 F') eO.surjective v'.asIdeal, h,
          Ideal.map_bot] }
  have hv : v ∉ placesOf 𝔪 := by
    intro h
    apply hv'
    change 𝔪.map eO ≤ v'.asIdeal
    rw [← map_equiv_coe]
    exact Ideal.map_le_iff_le_comap.2 h
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v x (hx v hv)
  have hd : eO d ∉ v'.asIdeal := d.2
  have hnd' : e x * algebraMap (𝓞 F') F' (eO d) = algebraMap (𝓞 F') F' (eO n) := by
    have := congrArg e hnd
    rw [map_mul] at this
    exact this
  have h1 : v'.valuation F' (algebraMap (𝓞 F') F' (eO d)) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hd
  have h2 : v'.valuation F' (algebraMap (𝓞 F') F' (eO n)) ≤ 1 := v'.valuation_le_one _
  rw [← hnd', map_mul, h1, mul_one] at h2
  exact h2

/-- The ring `R = 𝓞_S` transports along `e`. -/
def sIntEquiv (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) :
    SInt 𝔪 ≃+* SInt (𝔪.map (RingOfIntegers.mapRingEquiv e)) where
  toFun x := ⟨e x, mem_integer_map e 𝔪 x x.2⟩
  invFun y := ⟨e.symm y, by
    have := mem_integer_map e.symm (𝔪.map (RingOfIntegers.mapRingEquiv e)) y y.2
    rwa [mapRingEquiv_symm, map_equiv_symm_map] at this⟩
  left_inv x := Subtype.ext (e.symm_apply_apply _)
  right_inv y := Subtype.ext (e.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul e _ _)
  map_add' x y := Subtype.ext (map_add e _ _)

@[simp] theorem sIntEquiv_coe (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ((sIntEquiv e 𝔪 x : SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))) : F') = e x := rfl

@[simp] theorem sIntEquiv_symm_coe (e : F ≃+* F') (𝔪 : Ideal (𝓞 F))
    (y : SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))) :
    (((sIntEquiv e 𝔪).symm y : SInt 𝔪) : F) = e.symm y := rfl

theorem map_map_sIntEquiv (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) (I : Ideal (𝓞 F)) :
    (I.map (algebraMap (𝓞 F) (SInt 𝔪))).map (sIntEquiv e 𝔪) =
      (I.map (RingOfIntegers.mapRingEquiv e)).map
        (algebraMap (𝓞 F') (SInt (𝔪.map (RingOfIntegers.mapRingEquiv e)))) := by
  show Ideal.map ((sIntEquiv e 𝔪 : SInt 𝔪 →+* SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))))
      (I.map (algebraMap (𝓞 F) (SInt 𝔪))) =
    Ideal.map (algebraMap (𝓞 F') (SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))))
      (I.map ((RingOfIntegers.mapRingEquiv e : 𝓞 F →+* 𝓞 F')))
  rw [Ideal.map_map, Ideal.map_map]
  congr 1

theorem absNorm_map_equiv (e : F ≃+* F') (I : Ideal (𝓞 F)) :
    Ideal.absNorm (I.map (RingOfIntegers.mapRingEquiv e)) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I _ (RingOfIntegers.mapRingEquiv e) rfl).toEquiv).symm

theorem isExterior_map (e : F ≃+* F') {𝔪 I : Ideal (𝓞 F)} (h : IsExterior 𝔪 I) :
    IsExterior (𝔪.map (RingOfIntegers.mapRingEquiv e)) (I.map (RingOfIntegers.mapRingEquiv e)) := by
  refine ⟨fun h0 => h.1 ?_, ?_⟩
  · exact (Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.mapRingEquiv e).injective).1 h0
  · rw [← Ideal.map_sup, h.2, Ideal.map_top]

/-! ### Uniqueness of the sixth root of unity modulo `P` -/

theorem eq_of_pow_six {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R) (h6 : (6 : R) ∉ Q)
    {a b : R} (ha : a ^ 6 = 1) (hb : b ^ 6 = 1) (hab : a - b ∈ Q) : a = b := by
  set η := b * a ^ 5 with hη
  have h1 : 1 - η ∈ Q := by
    have : 1 - η = a ^ 5 * (a - b) := by rw [hη]; linear_combination (-1 : R) * ha
    rw [this]; exact Q.mul_mem_left _ hab
  by_cases hη1 : η = 1
  · have : b = a := calc
        b = b * a ^ 6 := by rw [ha, mul_one]
        _ = (b * a ^ 5) * a := by ring
        _ = a := by rw [← hη, hη1, one_mul]
    exact this.symm
  · exfalso
    have hη6 : η ^ 6 = 1 := by
      rw [hη]
      calc (b * a ^ 5) ^ 6 = b ^ 6 * (a ^ 6) ^ 5 := by ring
        _ = 1 := by rw [ha, hb]; ring
    have hsum : 1 + η + η ^ 2 + η ^ 3 + η ^ 4 + η ^ 5 = 0 := by
      have : (η - 1) * (1 + η + η ^ 2 + η ^ 3 + η ^ 4 + η ^ 5) = 0 := by
        linear_combination hη6
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (sub_eq_zero.1 h) hη1
      · exact h
    apply h6
    have : (6 : R) = (1 - η) * (5 + 4 * η + 3 * η ^ 2 + 2 * η ^ 3 + η ^ 4) +
        (1 + η + η ^ 2 + η ^ 3 + η ^ 4 + η ^ 5) := by ring
    rw [this, hsum, add_zero]
    exact Q.mul_mem_right _ h1

/-! ### The residue symbol transports -/

theorem sexticResidueSymbol_transport (e : F ≃+* F') (ι : F →+* ℂ) (𝔪 P : Ideal (𝓞 F))
    (h6 : P ⊔ Ideal.span {6} = ⊤) (x : SInt 𝔪) :
    sexticResidueSymbol (ι.comp (e.symm : F' →+* F)) (𝔪.map (RingOfIntegers.mapRingEquiv e))
        (P.map (RingOfIntegers.mapRingEquiv e)) (sIntEquiv e 𝔪 x) =
      sexticResidueSymbol ι 𝔪 P x := by
  classical
  set eO := RingOfIntegers.mapRingEquiv e
  set eS := sIntEquiv e 𝔪
  set f := algebraMap (𝓞 F) (SInt 𝔪)
  set f' := algebraMap (𝓞 F') (SInt (𝔪.map eO))
  set Q := P.map f
  have hQ' : (P.map eO).map f' = Q.map eS := (map_map_sIntEquiv e 𝔪 P).symm
  have hmem : ∀ y : SInt 𝔪, eS y ∈ (P.map eO).map f' ↔ y ∈ Q := fun y => by
    rw [hQ', mem_map_equiv, RingEquiv.symm_apply_apply]
  have hN : Ideal.absNorm (P.map eO) = Ideal.absNorm P := absNorm_map_equiv e P
  unfold sexticResidueSymbol
  simp only [Ideal.Quotient.eq_zero_iff_mem]
  by_cases hx : x ∈ Q
  · rw [if_pos hx, if_pos ((hmem x).2 hx)]
  rw [if_neg hx, if_neg (fun h => hx ((hmem x).1 h)), hN]
  set k := (Ideal.absNorm P - 1) / 6
  -- `6 ∉ Q`
  have h6Q : (6 : SInt 𝔪) ∉ Q := by
    intro h6m
    apply hx
    have : Q = ⊤ := by
      rw [eq_top_iff, ← Ideal.map_top f, ← h6, Ideal.map_sup]
      refine sup_le le_rfl ?_
      rw [Ideal.map_span, Set.image_singleton, map_ofNat, Ideal.span_le,
        Set.singleton_subset_iff]
      exact h6m
    rw [this]; trivial
  have hC : ∀ ζ : 𝓞 F, (ζ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ) = Ideal.Quotient.mk Q x ^ k) ↔
      ((eO ζ) ^ 6 = 1 ∧ Ideal.Quotient.mk ((P.map eO).map f') (f' (eO ζ)) =
        Ideal.Quotient.mk ((P.map eO).map f') (eS x) ^ k) := by
    intro ζ
    apply and_congr
    · rw [← map_pow, ← map_one eO]
      exact eO.injective.eq_iff.symm
    · rw [← map_pow, ← map_pow, Ideal.Quotient.eq, Ideal.Quotient.eq, ← map_pow eS,
        show f' (eO ζ) = eS (f ζ) from rfl, ← map_sub, hmem]
  have huniq : ∀ ζ₁ ζ₂ : 𝓞 F, (ζ₁ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ₁) = Ideal.Quotient.mk Q x ^ k) →
      (ζ₂ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ₂) = Ideal.Quotient.mk Q x ^ k) → ζ₁ = ζ₂ := by
    intro ζ₁ ζ₂ h1 h2
    have hsub : f ζ₁ - f ζ₂ ∈ Q := by
      rw [← Ideal.Quotient.eq, h1.2, h2.2]
    have := eq_of_pow_six Q h6Q (by rw [← map_pow, h1.1, map_one])
      (by rw [← map_pow, h2.1, map_one]) hsub
    have h' : ((f ζ₁ : SInt 𝔪) : F) = ((f ζ₂ : SInt 𝔪) : F) := by rw [this]
    exact RingOfIntegers.ext h'
  by_cases h : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ) = Ideal.Quotient.mk Q x ^ k
  · have h' : ∃ ζ' : 𝓞 F', ζ' ^ 6 = 1 ∧ Ideal.Quotient.mk ((P.map eO).map f') (f' ζ') =
        Ideal.Quotient.mk ((P.map eO).map f') (eS x) ^ k :=
      ⟨eO h.choose, (hC _).1 h.choose_spec⟩
    rw [dif_pos h, dif_pos h']
    have hspec : eO (eO.symm h'.choose) = h'.choose := eO.apply_symm_apply _
    have hC' := (hC (eO.symm h'.choose)).2 (by rw [hspec]; exact h'.choose_spec)
    have := huniq _ _ hC' h.choose_spec
    rw [← this]
    simp [eO]
  · have h' : ¬ ∃ ζ' : 𝓞 F', ζ' ^ 6 = 1 ∧ Ideal.Quotient.mk ((P.map eO).map f') (f' ζ') =
        Ideal.Quotient.mk ((P.map eO).map f') (eS x) ^ k := by
      rintro ⟨ζ', hζ'⟩
      apply h
      refine ⟨eO.symm ζ', (hC _).2 ?_⟩
      rw [eO.apply_symm_apply]; exact hζ'
    rw [dif_neg h, dif_neg h']

/-! ### `AllowedGen` transports -/

/-- `SmallPrimesDvd` transports. -/
theorem smallPrimesDvd_map (e : F ≃+* F') {N₀ : ℕ} {𝔪 : Ideal (𝓞 F)} (h : SmallPrimesDvd N₀ 𝔪) :
    SmallPrimesDvd N₀ (𝔪.map (RingOfIntegers.mapRingEquiv e)) := by
  set eO := RingOfIntegers.mapRingEquiv e
  intro P' hP' hP'0 hN
  set P := P'.map eO.symm
  have hPP : P.map eO = P' := by
    have := map_equiv_symm_map eO.symm P'
    rwa [RingEquiv.symm_symm] at this
  have hP : P.IsPrime := Ideal.map_isPrime_of_equiv eO.symm
  have hP0 : P ≠ ⊥ := fun h0 => hP'0 (by rw [← hPP, h0, Ideal.map_bot])
  have hNP : Ideal.absNorm P ≤ N₀ := by rw [← absNorm_map_equiv e P, hPP]; exact hN
  rw [← hPP]
  exact (map_equiv_le_iff eO).2 (h P hP hP0 hNP)

end C0R

end ArtinPrimitiveRoots

end
end

section
section
/-! C0Y: valuations of prime generators in `SInt 𝔪` and the sextic residue symbol. -/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace C0Y

variable {F : Type} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem sInt_val_le_one (s : SInt 𝔪) (w : HeightOneSpectrum (𝓞 F)) (hw : ¬ 𝔪 ≤ w.asIdeal) :
    w.valuation F (s : F) ≤ 1 :=
  s.2 w hw

theorem coe_algebraMap_sInt (a : 𝓞 F) :
    ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) = algebraMap (𝓞 F) F a := rfl

/-- Elements of `P · SInt` have `v_P < 1`. -/
theorem val_lt_one_of_mem_map (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal)
    {z : SInt 𝔪} (hz : z ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.valuation F (z : F) < 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [coe_algebraMap_sInt]
    exact (v.valuation_lt_one_iff_mem (K := F) a).mpr ha
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Subalgebra.coe_add]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  | smul a x _ hx =>
    simp only [smul_eq_mul, Subalgebra.coe_mul, map_mul]
    calc v.valuation F (a : F) * v.valuation F (x : F) ≤ 1 * v.valuation F (x : F) :=
          mul_le_mul_left (sInt_val_le_one a v hv) _
      _ < 1 := by rw [one_mul]; exact hx

/-- Valuations of a generator of `P · SInt`. -/
theorem val_generator (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) (p : SInt 𝔪)
    (hp : Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.valuation F (p : F) = WithZero.exp (-1 : ℤ) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ w.asIdeal → w ≠ v → w.valuation F (p : F) = 1 := by
  have hpmem : p ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hp]; exact Ideal.subset_span rfl
  have hlt := val_lt_one_of_mem_map v hv hpmem
  -- every `a ∈ P` is a multiple of `p` in `SInt`
  have hdiv : ∀ a ∈ v.asIdeal, ∃ s : SInt 𝔪, algebraMap (𝓞 F) F a = (p : F) * (s : F) := by
    intro a ha
    have : algebraMap (𝓞 F) (SInt 𝔪) a ∈ Ideal.span {p} := by
      rw [hp]; exact Ideal.mem_map_of_mem _ ha
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp this
    refine ⟨s, ?_⟩
    rw [← coe_algebraMap_sInt (𝔪 := 𝔪), ← hs, Subalgebra.coe_mul, mul_comm]
  refine ⟨?_, fun w hw hwv => ?_⟩
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer' F
    have hπmem : π ∈ v.asIdeal := by
      rw [← v.valuation_lt_one_iff_mem (K := F), hπ]; exact by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    obtain ⟨s, hs⟩ := hdiv π hπmem
    have h1 : v.valuation F (p : F) * v.valuation F (s : F) = WithZero.exp (-1 : ℤ) := by
      rw [← map_mul, ← hs, hπ]
    have hs1 := sInt_val_le_one s v hv
    have hp0 : v.valuation F (p : F) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h1; exact WithZero.exp_ne_zero h1.symm
    have hge : WithZero.exp (-1 : ℤ) ≤ v.valuation F (p : F) := by
      rw [← h1]; exact mul_le_of_le_one_right' hs1
    have hle : v.valuation F (p : F) ≤ WithZero.exp (-1 : ℤ) := by
      obtain ⟨k, hk⟩ := WithZero.ne_zero_iff_exists.mp hp0
      rw [← hk] at hlt ⊢
      rw [show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp 0 from rfl] at hlt
      have : (k : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd k) := rfl
      rw [this, WithZero.exp_lt_exp] at hlt
      rw [this, WithZero.exp_le_exp]
      omega
    exact le_antisymm hle hge
  · -- `P ⊄ w`
    have hnle : ¬ v.asIdeal ≤ w.asIdeal := by
      intro hle
      have := v.isMaximal.eq_of_le w.isPrime.ne_top hle
      exact hwv (HeightOneSpectrum.ext this.symm)
    obtain ⟨a, ha, haw⟩ := Set.not_subset.mp hnle
    obtain ⟨s, hs⟩ := hdiv a ha
    have h1 : w.valuation F (p : F) * w.valuation F (s : F) = 1 := by
      rw [← map_mul, ← hs]; exact (w.valuation_eq_one_iff_notMem (K := F)).mpr haw
    have hp1 := sInt_val_le_one p w hw
    have hs1 := sInt_val_le_one s w hw
    by_contra hne
    have hlt : w.valuation F (p : F) < 1 := lt_of_le_of_ne hp1 hne
    have : w.valuation F (p : F) * w.valuation F (s : F) < 1 :=
      lt_of_lt_of_le (mul_lt_one_of_lt_of_le hlt hs1) le_rfl
    rw [h1] at this
    exact lt_irrefl _ this

/-- Elements of `SInt` with `v_P < 1` lie in `P · SInt` (given a generator). -/
theorem mem_map_of_val_lt_one (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) (p : SInt 𝔪)
    (hp : Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) (z : SInt 𝔪)
    (hz : v.valuation F (z : F) < 1) : z ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  obtain ⟨hpv, hpw⟩ := val_generator v hv p hp
  have hp0 : (p : F) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hpv; exact WithZero.exp_ne_zero hpv.symm
  have hq : (z : F) / (p : F) ∈ (placesOf 𝔪).integer F := by
    intro w hw
    by_cases hwv : w = v
    · subst hwv
      rw [map_div₀, hpv]
      by_cases hz0 : w.valuation F (z : F) = 0
      · rw [hz0, zero_div]; exact zero_le
      obtain ⟨k, hk⟩ := WithZero.ne_zero_iff_exists.mp hz0
      rw [← hk] at hz ⊢
      have e : (k : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd k) := rfl
      rw [e, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hz
      rw [e, ← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    · rw [map_div₀, hpw w hw hwv, div_one]
      exact sInt_val_le_one z w hw
  have : z = p * ⟨(z : F) / (p : F), hq⟩ := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul]
    field_simp
  rw [← hp, this]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/-- The sextic residue symbol at an exterior prime with generator: `6 ∣ N P − 1`, and
`χ_P(y) = ι ξ` for the sixth root of unity `ξ ≡ y^{(N P − 1)/6} (mod P)`. -/
theorem sextic_spec (ι : F →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal)
    (p : SInt 𝔪) (hp : Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (h6 : (6 : 𝓞 F) ∉ v.asIdeal) (y : SInt 𝔪)
    (hy : v.valuation F (y : F) = 1) :
    6 ∣ Ideal.absNorm v.asIdeal - 1 ∧ ∃ ξ : 𝓞 F, ξ ^ 6 = 1 ∧
      v.valuation F ((y : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) - algebraMap (𝓞 F) F ξ) < 1 ∧
      sexticResidueSymbol ι 𝔪 v.asIdeal y = ι (algebraMap (𝓞 F) F ξ) := by
  classical
  set P := v.asIdeal with hPdef
  letI : Field (𝓞 F ⧸ P) := Ideal.Quotient.field P
  haveI : Finite (𝓞 F ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P v.ne_bot
  letI : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 F ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hinj : ∀ a b : 𝓞 F, a ^ 6 = 1 → b ^ 6 = 1 →
      Ideal.Quotient.mk P a = Ideal.Quotient.mk P b → a = b := fun a b ha hb h =>
    C0R.eq_of_pow_six P h6 ha hb (Ideal.Quotient.eq.mp h)
  have hη : IsPrimitiveRoot (Ideal.Quotient.mk P z6) 6 := by
    refine ⟨by rw [← map_pow, hz6.pow_eq_one, map_one], fun l hl => ?_⟩
    have : z6 ^ l = 1 := hinj _ _ (by rw [← pow_mul, mul_comm, pow_mul, hz6.pow_eq_one, one_pow])
      (one_pow 6) (by rw [map_pow, hl, map_one])
    exact hz6.dvd_of_pow_eq_one l this
  have h6N : 6 ∣ Ideal.absNorm P - 1 := by
    have := FiniteField.pow_card_sub_one_eq_one (Ideal.Quotient.mk P z6) (hη.ne_zero (by norm_num))
    rw [hcard] at this
    exact hη.dvd_of_pow_eq_one _ this
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v (y : F) hy.le
  have hd : (d : 𝓞 F) ∉ P := d.2
  have hdv : v.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F)).mpr hd
  have hdF : algebraMap (𝓞 F) F d ≠ 0 := by
    intro h0; rw [h0, map_zero] at hdv; exact zero_ne_one hdv
  have hn : (n : 𝓞 F) ∉ P := by
    rw [← v.valuation_eq_one_iff_notMem (K := F), ← hnd, map_mul, hy, hdv, one_mul]
  set k := (Ideal.absNorm P - 1) / 6 with hk
  set u : 𝓞 F ⧸ P := Ideal.Quotient.mk P n * (Ideal.Quotient.mk P d)⁻¹ with hu
  have hmd : Ideal.Quotient.mk P (d : 𝓞 F) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hmn : Ideal.Quotient.mk P n ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hu0 : u ≠ 0 := mul_ne_zero hmn (inv_ne_zero hmd)
  have hu6 : (u ^ k) ^ 6 = 1 := by
    rw [← pow_mul, hk, Nat.div_mul_cancel h6N, ← hcard]
    exact FiniteField.pow_card_sub_one_eq_one u hu0
  obtain ⟨i, -, hi⟩ := hη.eq_pow_of_pow_eq_one hu6
  set ξ := z6 ^ i with hξ
  have hξ6 : ξ ^ 6 = 1 := by rw [hξ, ← pow_mul, mul_comm, pow_mul, hz6.pow_eq_one, one_pow]
  have hcong : n ^ k - ξ * (d : 𝓞 F) ^ k ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_pow, map_pow, map_pow, hi,
      hu, mul_pow, inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hmd), mul_one, sub_self]
  have hval : v.valuation F ((y : F) ^ k - algebraMap (𝓞 F) F ξ) < 1 := by
    have hyd : (y : F) = algebraMap (𝓞 F) F n / algebraMap (𝓞 F) F d := by
      rw [← hnd, mul_div_cancel_right₀ _ hdF]
    have : (y : F) ^ k - algebraMap (𝓞 F) F ξ =
        algebraMap (𝓞 F) F (n ^ k - ξ * (d : 𝓞 F) ^ k) / (algebraMap (𝓞 F) F d) ^ k := by
      rw [hyd, eq_div_iff (pow_ne_zero _ hdF)]
      simp only [map_sub, map_mul, map_pow]
      rw [sub_mul, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hdF)]
    rw [this, map_div₀, map_pow, hdv, one_pow, div_one]
    exact (v.valuation_lt_one_iff_mem (K := F) _).mpr hcong
  refine ⟨h6N, ξ, hξ6, hval, ?_⟩
  set f := algebraMap (𝓞 F) (SInt 𝔪)
  set Q := P.map f
  have hyQ : y ∉ Q := fun h => by
    have := val_lt_one_of_mem_map v hv h; rw [hy] at this; exact lt_irrefl _ this
  have h6Q : (6 : SInt 𝔪) ∉ Q := by
    intro h
    have := val_lt_one_of_mem_map v hv h
    have e : ((6 : SInt 𝔪) : F) = algebraMap (𝓞 F) F 6 := by rw [map_ofNat]; rfl
    rw [e, (v.valuation_eq_one_iff_notMem (K := F)).mpr h6] at this
    exact lt_irrefl _ this
  have hex : f ξ - y ^ k ∈ Q := by
    apply mem_map_of_val_lt_one v hv p hp
    have e : ((f ξ - y ^ k : SInt 𝔪) : F) = -((y : F) ^ k - algebraMap (𝓞 F) F ξ) := by
      simp [f, coe_algebraMap_sInt]
    rw [e, Valuation.map_neg]; exact hval
  unfold sexticResidueSymbol
  rw [if_neg (by rwa [Ideal.Quotient.eq_zero_iff_mem])]
  have hE : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ) = Ideal.Quotient.mk Q y ^ k :=
    ⟨ξ, hξ6, by rw [← map_pow, Ideal.Quotient.eq]; exact hex⟩
  rw [dif_pos hE]
  have hch := hE.choose_spec
  have hsub : f hE.choose - f ξ ∈ Q := by
    rw [← Ideal.Quotient.eq, hch.2, ← map_pow, Ideal.Quotient.eq]
    have : y ^ k - f ξ = -(f ξ - y ^ k) := by ring
    rw [this]; exact Q.neg_mem hex
  have heq := C0R.eq_of_pow_six Q h6Q (by rw [← map_pow, hch.1, map_one])
    (by rw [← map_pow, hξ6, map_one]) hsub
  have : hE.choose = ξ := by
    have h' := congrArg (fun z : SInt 𝔪 => (z : F)) heq
    simp only [f, coe_algebraMap_sInt] at h'
    exact FaithfulSMul.algebraMap_injective (𝓞 F) F h'
  rw [this]

end C0Y

end
end
end

section
section
/-! # L3K_Bridge: `kummerL` is `L(s, ψ_u)` up to finitely many Euler factors at `S`

Setting (universe 0): `ζ` a primitive sixth root of unity in `F`, every prime containing `6`
contains `𝔪`, every exterior prime is principal in `R`, `u R = 𝔲 R` with `𝔲` exterior and
sixth-power-free, `u` not a sixth power. With `ψ = ψ_u`:
* exterior `v`: `localValue ψ v = χ_v(u)` (`v ∤ 𝔲`, unramified) and `ψ` is ramified at `v ∣ 𝔲`;
* `kummerL u = L(ψ) · ∏_{P ⊇ 𝔣𝔪, P + 𝔣 = 1} (1 − ψ(P) N P^{-s})` on `Re s > 1`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin ArtinPrimitiveRoots.L3K.KB UniqueFactorizationMonoid

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

variable {F : Type} [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 6) (ι : F →+* ℂ)
  {𝔪 : Ideal (𝓞 F)}

/-- The data of the bridge. -/
structure BridgeHyp (𝔪 : Ideal (𝓞 F)) (u : SInt 𝔪) (𝔲 : Ideal (𝓞 F)) : Prop where
  ne_bot : 𝔪 ≠ ⊥
  six : ∀ v : HeightOneSpectrum (𝓞 F), (6 : 𝓞 F) ∈ v.asIdeal → 𝔪 ≤ v.asIdeal
  prin : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal →
    ∃ p : SInt 𝔪, Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))
  gen : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪))
  sfree : IsSixthPowerFree 𝔲
  nonsix : ∀ b : F, b ^ 6 ≠ (u : F)

variable {u : SInt 𝔪} {𝔲 : Ideal (𝓞 F)}

lemma BridgeHyp.ne_zero (h : BridgeHyp 𝔪 u 𝔲) : (u : F) ≠ 0 := fun h0 =>
  h.nonsix 0 (by rw [h0]; ring)

/-- `u` as a unit of `F`. -/
def uUnit (h : BridgeHyp 𝔪 u 𝔲) : Fˣ := Units.mk0 (u : F) h.ne_zero

/-- `ζ` as an algebraic integer. -/
def z6 : 𝓞 F := ⟨ζ, IsIntegral.of_pow (by norm_num : 0 < 6) (by rw [hζ.pow_eq_one]; exact isIntegral_one)⟩

lemma z6_prim : IsPrimitiveRoot (z6 hζ) 6 :=
  (IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 F) F) (by
    show IsPrimitiveRoot ζ 6; exact hζ) (FaithfulSMul.algebraMap_injective _ _))

lemma six_not_mem (h : BridgeHyp 𝔪 u 𝔲) {v : HeightOneSpectrum (𝓞 F)} (hv : ¬ 𝔪 ≤ v.asIdeal) :
    (6 : 𝓞 F) ∉ v.asIdeal := fun h6 => hv (h.six v h6)

/-- **Exterior primes away from `𝔲`.** -/
theorem localValue_eq_sextic (h : BridgeHyp 𝔪 u 𝔲) {v : HeightOneSpectrum (𝓞 F)}
    (hv : ¬ 𝔪 ≤ v.asIdeal) (hv𝔲 : ¬ 𝔲 ≤ v.asIdeal) :
    ArtinL.Abelian.IsUnramifiedAt (psi F hζ ι (uUnit h)) v ∧
      ArtinL.Abelian.localValue (psi F hζ ι (uUnit h)) v = sexticResidueSymbol ι 𝔪 v.asIdeal u := by
  have hval : v.valuation F ((uUnit h : Fˣ) : F) = 1 := val_eq_one v hv h.gen hv𝔲
  have h6 := six_not_mem h hv
  have h6' : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal := by exact_mod_cast h6
  have hun := isUnramifiedAt_psi hζ ι (uUnit h) v h6' hval
  obtain ⟨p, hp⟩ := h.prin v hv
  obtain ⟨-, ξ, hξ6, hcong, hsx⟩ := C0Y.sextic_spec ι v hv p hp (z6_prim hζ) h6 u hval
  refine ⟨hun, ?_⟩
  rw [ArtinL.Abelian.localValue, if_pos hun, hsx,
    psi_artinFrob hζ ι (uUnit h) v h6' hval (algebraMap (𝓞 F) F ξ) (by rw [← map_pow, hξ6, map_one])
      hcong]

/-- **Primes dividing `𝔲` are ramified**, and there `χ_v(u) = 0`. -/
theorem ramified_of_le (h : BridgeHyp 𝔪 u 𝔲) {v : HeightOneSpectrum (𝓞 F)}
    (hv : ¬ 𝔪 ≤ v.asIdeal) (hv𝔲 : 𝔲 ≤ v.asIdeal) :
    ¬ ArtinL.Abelian.IsUnramifiedAt (psi F hζ ι (uUnit h)) v ∧
      sexticResidueSymbol ι 𝔪 v.asIdeal u = 0 := by
  refine ⟨not_isUnramifiedAt_psi hζ ι (uUnit h) v (val_ne_exp_six v hv h.sfree h.gen hv𝔲), ?_⟩
  obtain ⟨p, hp⟩ := h.prin v hv
  have hlt : v.valuation F (u : F) < 1 := by
    have := val_le_of_le v hv h.gen (e := 1) (by simpa using hv𝔲)
    refine this.trans_lt ?_
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by norm_num)
  have hmem := C0Y.mem_map_of_val_lt_one v hv p hp u hlt
  unfold sexticResidueSymbol
  rw [if_pos (Ideal.Quotient.eq_zero_iff_mem.2 hmem)]

lemma residueSymbol_mul' (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 (I * J) x = residueSymbol ι 𝔪 I x * residueSymbol ι 𝔪 J x := by
  unfold residueSymbol
  rw [normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

lemma residueSymbol_prime' {P : Ideal (𝓞 F)} (hP : Irreducible P) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 P x = sexticResidueSymbol ι 𝔪 P x := by
  unfold residueSymbol
  rw [normalizedFactors_irreducible hP, normalize_eq]; simp

lemma residueSymbol_top' (x : SInt 𝔪) : residueSymbol ι 𝔪 ⊤ x = 1 := by
  unfold residueSymbol
  rw [← Ideal.one_eq_top, normalizedFactors_one]; simp

lemma isExterior_mul_iff {I J : Ideal (𝓞 F)} :
    IsExterior 𝔪 (I * J) ↔ IsExterior 𝔪 I ∧ IsExterior 𝔪 J := by
  unfold IsExterior
  have hb : I * J ≠ ⊥ ↔ I ≠ ⊥ ∧ J ≠ ⊥ := by
    simp only [ne_eq, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
  rw [hb, C3A.sup_mul_eq_top_iff]; tauto

lemma sup_mul_top {P I J : Ideal (𝓞 F)} : P ⊔ I * J = ⊤ ↔ P ⊔ I = ⊤ ∧ P ⊔ J = ⊤ := by
  rw [sup_comm, C3A.sup_mul_eq_top_iff, sup_comm I, sup_comm J]

variable (hK : ∀ w : InfinitePlace F, w.IsComplex)

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3W_Twist: the twisted character `ω = η · conj χ_•(u)`

With `𝔠 = 𝔣(ψ_u)` and `𝔤 = 𝔪 𝔠`: `ωH = η · conj psiH` is a Hecke character mod `𝔤`, and
`twistedL ι η u = L(s, ωH)` on `Re s > 1`. At an exterior prime `P₀ ∣ 𝔲` the conductor minimality of
`ψ_u` (41aa80ff) and the Chinese remainder theorem give `β ≡ 1 (mod 𝔪 𝔠/P₀^k)`, prime to `𝔤`,
with `ω((β)) ≠ 1` (`exists_witness`). -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply nonZeroDivisors
  UniqueFactorizationMonoid

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3W

open L3K

variable {F : Type} [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 6) (ι : F →+* ℂ)
  {𝔪 : Ideal (𝓞 F)} {u : SInt 𝔪} {𝔲 : Ideal (𝓞 F)} (hK : ∀ w : InfinitePlace F, w.IsComplex)

/-- On exterior ideals the residue symbol is `psiH`. -/
lemma residueSymbol_eq_psiH (h : BridgeHyp 𝔪 u 𝔲) (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) :
    residueSymbol ι 𝔪 I u = (psiH (psi F hζ ι (uUnit h)) hK).toFun I := by
  revert hI
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro hI; exact absurd rfl hI.1
  | h₂ x hx =>
    intro _
    rw [Ideal.isUnit_iff.1 hx, residueSymbol_top', T12B.toFun_top]
  | h₃ a p ha hp ih =>
    intro hI
    obtain ⟨hpE, haE⟩ := isExterior_mul_iff.1 hI
    rw [residueSymbol_mul' ι _ _ hpE.1 haE.1, (psiH _ hK).map_mul', ih haE]
    congr 1
    set v := HeightOneSpectrum.ofPrime hp
    have hvm : ¬ 𝔪 ≤ v.asIdeal := by
      intro hm; apply v.isPrime.ne_top; rw [eq_top_iff, ← hpE.2]; exact sup_le le_rfl hm
    show residueSymbol ι 𝔪 v.asIdeal u = (psiH _ hK).toFun v.asIdeal
    rw [residueSymbol_prime' ι v.irreducible, psiH_prime]
    by_cases hv𝔲 : 𝔲 ≤ v.asIdeal
    · obtain ⟨hram, hs⟩ := ramified_of_le hζ ι h hvm hv𝔲
      rw [hs, ArtinL.Abelian.localValue, if_neg hram]
    · exact (localValue_eq_sextic hζ ι h hvm hv𝔲).2.symm

/-- `ωH = η · conj psiH` mod `𝔪 𝔠`. -/
def omegaH (h : BridgeHyp 𝔪 u 𝔲) (η : HeckeChar F 𝔪) :
    HeckeChar F (𝔪 * ArtinL.Abelian.conductor (psi F hζ ι (uUnit h))) where
  toFun I := η.toFun I * (starRingEnd ℂ) ((psiH (psi F hζ ι (uUnit h)) hK).toFun I)
  map_mul' I J := by
    rw [η.map_mul', (psiH _ hK).map_mul', map_mul]; ring
  eq_zero_iff' I := by
    rw [mul_eq_zero, map_eq_zero, η.eq_zero_iff', (psiH _ hK).eq_zero_iff', ne_eq, ne_eq, ne_eq,
      sup_mul_top]
    tauto
  map_principal' α hα h1 := by
    have h1m : α - 1 ∈ 𝔪 :=
      Ideal.mul_le_left (I := 𝔪) (J := ArtinL.Abelian.conductor (psi F hζ ι (uUnit h))) h1
    have h1c : α - 1 ∈ ArtinL.Abelian.conductor (psi F hζ ι (uUnit h)) :=
      Ideal.mul_le_right (I := 𝔪) (J := ArtinL.Abelian.conductor (psi F hζ ι (uUnit h))) h1
    rw [η.map_principal' α hα h1m, (psiH _ hK).map_principal' α hα h1c, map_one, mul_one]

lemma twistedL_eq (h : BridgeHyp 𝔪 u 𝔲) (η : HeckeChar F 𝔪) {ξ : ℂ} (hξ : 1 < ξ.re) :
    twistedL ι η u ξ = (omegaH hζ ι hK h η).LSeries ξ := by
  classical
  have h𝔤 : 𝔪 * ArtinL.Abelian.conductor (psi F hζ ι (uUnit h)) ≠ ⊥ :=
    mul_ne_zero h.ne_bot (ArtinL.Abelian.conductor_ne_bot _)
  rw [T12B.lseries_eq_tsum _ (T12B.norm_le_one h𝔤 _) hξ, twistedL]
  rw [← tsum_subtype_eq_of_support_subset (s := {I | IsExterior 𝔪 I})
    (f := fun I : Ideal (𝓞 F) => T12B.gs (omegaH hζ ι hK h η) ξ I)]
  · refine tsum_congr fun I => ?_
    rw [T12B.gs, residueSymbol_eq_psiH hζ ι hK h I.1 I.2]
    rfl
  · intro I hI
    by_contra hne
    apply hI
    have : η.toFun I = 0 := by
      rw [η.eq_zero_iff']; by_contra hc; push Not at hc; exact hne ⟨hc.1, hc.2⟩
    show (η.toFun I * _) * _ = 0
    rw [this, zero_mul, zero_mul]

section Gen

variable {K : Type} [Field K] [NumberField K]

lemma pU_mul (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0) :
    principalUnit K (a * b) (mul_ne_zero ha hb) = principalUnit K a ha * principalUnit K b hb := by
  apply Units.ext
  rw [Units.val_mul, principalUnit_val, principalUnit_val, principalUnit_val,
    ← Ideal.span_singleton_mul_span_singleton, FractionalIdeal.coeIdeal_mul]

/-- Congruent elements prime to `𝔣` have the same class. -/
lemma same_class (hK : ∀ w : InfinitePlace K, w.IsComplex) {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    {α β : 𝓞 K} (hα : α ≠ 0) (hβ : β ≠ 0) (hcα : principalUnit K α hα ∈ coprimeToModulus K 𝔣)
    (hcβ : principalUnit K β hβ ∈ coprimeToModulus K 𝔣) (hab : β - α ∈ 𝔣) :
    NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K β hβ, hcβ⟩ =
      NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K α hα, hcα⟩ := by
  have hcnt : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      FractionalIdeal.count K v ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
    intro v hv
    have := ((mem_coprimeToModulus_iff K).1 hcα) v hv
    rwa [principalUnit_val] at this
  obtain ⟨c, hc⟩ := exists_mul_sub_one_mem_of_counts_zero K h𝔣 hα hcnt
  by_cases hc0 : c = 0
  · have h1 : (1 : 𝓞 K) ∈ 𝔣 := by
      have := Ideal.neg_mem_iff _ |>.2 hc; rw [hc0] at this; simpa using this
    have htop : 𝔣 = ⊤ := (Ideal.eq_top_iff_one _).2 h1
    rw [narrow_mem hK hβ (by rw [htop]; trivial) hcβ, narrow_mem hK hα (by rw [htop]; trivial) hcα]
  have hβc : β * c - 1 ∈ 𝔣 := by
    have : β * c - 1 = (β - α) * c + (α * c - 1) := by ring
    rw [this]; exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hab) hc
  have hcc : principalUnit K c hc0 ∈ coprimeToModulus K 𝔣 := by
    have h1 := principalUnit_mem_coprimeToModulus K (mul_ne_zero hα hc0) hc
    rw [pU_mul α c hα hc0] at h1
    have := mul_mem (inv_mem hcα) h1
    rwa [inv_mul_cancel_left] at this
  have e1 := narrow_mem hK (mul_ne_zero hα hc0) hc (principalUnit_mem_coprimeToModulus K _ hc)
  have e2 := narrow_mem hK (mul_ne_zero hβ hc0) hβc (principalUnit_mem_coprimeToModulus K _ hβc)
  have s1 : (⟨principalUnit K (α * c) (mul_ne_zero hα hc0),
      principalUnit_mem_coprimeToModulus K _ hc⟩ : ↥(coprimeToModulus K 𝔣)) =
      ⟨principalUnit K α hα, hcα⟩ * ⟨principalUnit K c hc0, hcc⟩ := Subtype.ext (pU_mul α c hα hc0)
  have s2 : (⟨principalUnit K (β * c) (mul_ne_zero hβ hc0),
      principalUnit_mem_coprimeToModulus K _ hβc⟩ : ↥(coprimeToModulus K 𝔣)) =
      ⟨principalUnit K β hβ, hcβ⟩ * ⟨principalUnit K c hc0, hcc⟩ := Subtype.ext (pU_mul β c hβ hc0)
  rw [s1, map_mul] at e1
  rw [s2, map_mul] at e2
  have e3 := e2.trans e1.symm
  calc _ = NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K β hβ, hcβ⟩ * NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K c hc0, hcc⟩ * (NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K c hc0, hcc⟩)⁻¹ := by group
    _ = _ := by rw [e3]; group

end Gen

lemma chiR_prim {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ) :
    ∀ 𝔣' : Ideal (𝓞 K), ArtinL.Abelian.conductor ψ ≤ 𝔣' → 𝔣' ≠ ArtinL.Abelian.conductor ψ →
      ∃ (α : 𝓞 K) (hα : α ≠ 0)
        (hc : principalUnit K α hα ∈ coprimeToModulus K (ArtinL.Abelian.conductor ψ)),
        α - 1 ∈ 𝔣' ∧ (∀ τ : K →+* ℝ, 0 < τ (α : K)) ∧
          chiR ψ (NarrowRayClassGroup.mk K (ArtinL.Abelian.conductor ψ)
            ⟨principalUnit K α hα, hc⟩) ≠ 1 :=
  (ArtinL.Abelian.exists_narrowRayClassChar_conductor_eq_localValue_u0 K M ψ).choose_spec.2.2.2

lemma sup_top_of_not_le {P I : Ideal (𝓞 F)} (hP : P.IsMaximal) (h : ¬ I ≤ P) : P ⊔ I = ⊤ := by
  by_contra hne
  exact h (le_trans le_sup_right (le_of_eq (hP.eq_of_le hne le_sup_left).symm))

/-- **The witness** at an exterior prime `P₀ ∣ 𝔲`. -/
theorem exists_witness (h : BridgeHyp 𝔪 u 𝔲) (η : HeckeChar F 𝔪) (P₀ : HeightOneSpectrum (𝓞 F))
    (hP₀m : ¬ 𝔪 ≤ P₀.asIdeal) (hP₀u : 𝔲 ≤ P₀.asIdeal) :
    ∃ 𝔠' : Ideal (𝓞 F), ¬ P₀.asIdeal ∣ 𝔠' ∧
      (∃ k : ℕ, ArtinL.Abelian.conductor (psi F hζ ι (uUnit h)) = P₀.asIdeal ^ k * 𝔠') ∧
      ∃ (β : 𝓞 F) (hβ : β ≠ 0)
        (hc : principalUnit F β hβ ∈
          coprimeToModulus F (𝔪 * ArtinL.Abelian.conductor (psi F hζ ι (uUnit h)))),
        β - 1 ∈ 𝔪 * 𝔠' ∧
        T12A.rayChar (omegaH hζ ι hK h η)
          (NarrowRayClassGroup.mk F _ ⟨principalUnit F β hβ, hc⟩) ≠ 1 := by
  classical
  set ψ := psi F hζ ι (uUnit h)
  set 𝔠 := ArtinL.Abelian.conductor ψ
  have h𝔠 : 𝔠 ≠ ⊥ := ArtinL.Abelian.conductor_ne_bot ψ
  have hram := (ramified_of_le hζ ι h hP₀m hP₀u).1
  have hP₀𝔠 : P₀.asIdeal ∣ 𝔠 := (ArtinL.Abelian.dvd_conductor_iff_not_isUnramifiedAt F _ ψ P₀).2 hram
  obtain ⟨k, 𝔠', hnd, hk⟩ := WfDvdMonoid.max_power_factor h𝔠 P₀.irreducible
  refine ⟨𝔠', hnd, ⟨k, hk⟩, ?_⟩
  have hk1 : k ≠ 0 := by
    rintro rfl; rw [pow_zero, one_mul] at hk; exact hnd (hk ▸ hP₀𝔠)
  have hle : 𝔠 ≤ 𝔠' := by rw [hk]; exact Ideal.mul_le_left (I := 𝔠') (J := P₀.asIdeal ^ k) |>.trans' (le_of_eq (mul_comm _ _))
  have hne : 𝔠' ≠ 𝔠 := fun he => hnd (he ▸ hP₀𝔠)
  obtain ⟨α, hα0, hcα, hα1, -, hχα⟩ := chiR_prim ψ 𝔠' hle hne
  -- CRT
  have hmax := P₀.isMaximal
  have hPm : P₀.asIdeal ⊔ 𝔪 = ⊤ := sup_top_of_not_le hmax hP₀m
  have hPc : P₀.asIdeal ⊔ 𝔠' = ⊤ := sup_top_of_not_le hmax (fun hle' => hnd (Ideal.dvd_iff_le.2 hle'))
  have hcop : IsCoprime (P₀.asIdeal ^ k) (𝔪 * 𝔠') := by
    apply IsCoprime.pow_left
    rw [Ideal.isCoprime_iff_sup_eq, sup_mul_top]; exact ⟨hPm, hPc⟩
  have hcop' : IsCoprime (P₀.asIdeal ^ k) 𝔠' := by
    apply IsCoprime.pow_left; rw [Ideal.isCoprime_iff_sup_eq]; exact hPc
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (show (1 : 𝓞 F) ∈ P₀.asIdeal ^ k ⊔ 𝔪 * 𝔠' by
    rw [Ideal.isCoprime_iff_sup_eq.1 hcop]; trivial)
  set β := α * q + p
  have hβ1 : β - 1 ∈ 𝔪 * 𝔠' := by
    have : β - 1 = (α - 1) * q := by simp only [β]; linear_combination hpq
    rw [this]; exact Ideal.mul_mem_left _ _ hq
  have hβα : β - α ∈ P₀.asIdeal ^ k := by
    have : β - α = p * (1 - α) := by simp only [β]; linear_combination α * hpq
    rw [this]; exact Ideal.mul_mem_right _ _ hp
  have hβα' : β - α ∈ 𝔠 := by
    have h2 : β - α ∈ 𝔠' := by
      have : β - α = (β - 1) - (α - 1) := by ring
      rw [this]; exact Ideal.sub_mem _ (Ideal.mul_le_right (I := 𝔪) (J := 𝔠') hβ1) hα1
    rw [hk, ← Ideal.inf_eq_mul_of_isCoprime hcop']
    exact ⟨hβα, h2⟩
  -- `α, β ∉ P₀`
  have hαP : α ∉ P₀.asIdeal := by
    intro hm
    have hsup := (T12A.mk0_mem_coprimeToModulus_iff (mem_nonZeroDivisors_of_ne_zero
      (T12A.span_ne_bot hα0))).1 hcα
    apply P₀.isPrime.ne_top
    rw [eq_top_iff, ← hsup]
    exact sup_le (by rwa [Ideal.span_singleton_le_iff_mem]) (Ideal.le_of_dvd hP₀𝔠)
  have hβP : β ∉ P₀.asIdeal := by
    intro hm
    apply hαP
    have := Ideal.sub_mem _ hm (Ideal.pow_le_self hk1 hβα)
    simpa using this
  have hβ0 : β ≠ 0 := fun h0 => hβP (h0 ▸ Ideal.zero_mem _)
  -- `β` prime to `𝔤 = 𝔪 𝔠`
  have hsβ : Ideal.span {β} ⊔ 𝔪 * 𝔠 = ⊤ := by
    have h1 : Ideal.span {β} ⊔ 𝔪 * 𝔠' = ⊤ := T12A.span_sup_eq_top hβ1
    have h2 : Ideal.span {β} ⊔ P₀.asIdeal ^ k = ⊤ := by
      rw [← Ideal.isCoprime_iff_sup_eq]
      apply IsCoprime.pow_right
      rw [Ideal.isCoprime_iff_sup_eq, sup_comm]
      exact sup_top_of_not_le hmax (by rwa [Ideal.span_singleton_le_iff_mem])
    rw [sup_mul_top] at h1 ⊢
    refine ⟨h1.1, ?_⟩
    rw [hk, sup_mul_top]; exact ⟨h2, h1.2⟩
  have hcβ : principalUnit F β hβ0 ∈ coprimeToModulus F (𝔪 * 𝔠) :=
    (T12A.mk0_mem_coprimeToModulus_iff _).2 hsβ
  refine ⟨β, hβ0, hcβ, hβ1, ?_⟩
  have hβm : β - 1 ∈ 𝔪 := Ideal.mul_le_left (I := 𝔪) (J := 𝔠') hβ1
  have hcβ𝔠 : principalUnit F β hβ0 ∈ coprimeToModulus F 𝔠 :=
    (T12A.mk0_mem_coprimeToModulus_iff _).2 (sup_mul_top.1 hsβ).2
  have hval : T12A.rayChar (omegaH hζ ι hK h η)
      (NarrowRayClassGroup.mk F _ ⟨principalUnit F β hβ0, hcβ⟩) =
      (starRingEnd ℂ) (chiR ψ (NarrowRayClassGroup.mk F 𝔠 ⟨principalUnit F α hα0, hcα⟩)) := by
    rw [show (⟨principalUnit F β hβ0, hcβ⟩ : ↥(coprimeToModulus F (𝔪 * 𝔠))) =
      ⟨FractionalIdeal.mk0 F ⟨Ideal.span {β}, mem_nonZeroDivisors_of_ne_zero (T12A.span_ne_bot hβ0)⟩,
        hcβ⟩ from rfl, T12A.rayChar_mk_ideal]
    show η.toFun _ * (starRingEnd ℂ) ((psiH ψ hK).toFun _) = _
    rw [η.map_principal' β hβ0 hβm, one_mul]
    congr 1
    have hc2 : Ideal.span {β} ≠ ⊥ ∧ Ideal.span {β} ⊔ 𝔠 = ⊤ :=
      ⟨T12A.span_ne_bot hβ0, (sup_mul_top.1 hsβ).2⟩
    show (if _ then _ else _) = _
    rw [if_pos hc2, T12A.cls, dif_pos hc2]
    congr 1
    exact same_class hK h𝔠 hα0 hβ0 hcα hcβ𝔠 hβα'
  rw [hval]
  intro h1
  apply hχα
  have := congrArg (starRingEnd ℂ) h1
  rwa [RCLike.conj_conj, map_one] at this

end L3W

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3W_Core: (8.3) for `L^S(ξ, η conj χ_•(u))`, `F : Type`, `𝔲 ≠ ⊤`

`ω = rayChar(ωH)` mod `𝔤 = 𝔪 𝔣(ψ_u)` has a primitive model `χ₀` mod `𝔣 ⊇ 𝔤` (L3W_Ray); every
exterior `P₀ ∣ 𝔲` divides `𝔣` (the witness of L3W_Twist), so `χ₀ ≠ 1` and the Euler factors between
`L(ωH)` and `L(χ₀)` sit at primes over `𝔪`. Then L3W_RConv/L3W_Abs give the bound. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3W

open L3K

section Gen

variable {K : Type} [Field K] [NumberField K]

/-- A finite Euler-factor product over primes containing `𝔪` is entire and `≤ 2^{n_𝔪}` on
`Re s ≥ 0`. -/
theorem efac_generic {𝔣 𝔪 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar K 𝔣)
    (B : Set (Ideal (𝓞 K))) (hB : B ⊆ {P : Ideal (𝓞 K) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P}) :
    Differentiable ℂ (fun s : ℂ => ∏ᶠ P ∈ B, (1 - χ.toFun P * (Ideal.absNorm P : ℂ) ^ (-s))) ∧
      ∀ s : ℂ, 0 ≤ s.re →
        ‖∏ᶠ P ∈ B, (1 - χ.toFun P * (Ideal.absNorm P : ℂ) ^ (-s))‖ ≤
          2 ^ (C3A.finite_primes_ge h𝔪).toFinset.card := by
  classical
  have hBf : B.Finite := (C3A.finite_primes_ge h𝔪).subset hB
  have heq : ∀ s : ℂ, ∏ᶠ P ∈ B, (1 - χ.toFun P * (Ideal.absNorm P : ℂ) ^ (-s)) =
      ∏ P ∈ hBf.toFinset, (1 - χ.toFun P * (Ideal.absNorm P : ℂ) ^ (-s)) := fun s =>
    finprod_mem_eq_finite_toFinset_prod _ hBf
  have hnorm := T12A.norm_heckeChar_le h𝔣 χ
  refine ⟨?_, fun s hs => ?_⟩
  · rw [funext heq]
    refine Differentiable.fun_finsetProd (𝕜 := ℂ) fun P hP => ?_
    have hP0 : (Ideal.absNorm P : ℂ) ≠ 0 := by
      have := (hB ((Set.Finite.mem_toFinset _).1 hP)).2.1
      exact_mod_cast (Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])).ne'
    exact (differentiable_const _).sub ((differentiable_const _).mul
      (fun s => (differentiableAt_id.neg).const_cpow (Or.inl hP0)))
  · rw [heq, norm_prod]
    have hcard : hBf.toFinset.card ≤ (C3A.finite_primes_ge h𝔪).toFinset.card :=
      Finset.card_le_card (Set.Finite.toFinset_subset_toFinset.2 hB)
    calc ∏ P ∈ hBf.toFinset, ‖1 - χ.toFun P * (Ideal.absNorm P : ℂ) ^ (-s)‖
        ≤ ∏ _P ∈ hBf.toFinset, (2 : ℝ) := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun P hP => ?_
          have hPn : 0 < Ideal.absNorm P := Nat.pos_of_ne_zero (by
            rw [Ne, Ideal.absNorm_eq_zero_iff]; exact (hB ((Set.Finite.mem_toFinset _).1 hP)).2.1)
          have h1 : ‖(Ideal.absNorm P : ℂ) ^ (-s)‖ ≤ 1 := by
            rw [Complex.norm_natCast_cpow_of_pos hPn, Complex.neg_re]
            exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hPn) (by linarith)
          calc _ ≤ ‖(1 : ℂ)‖ + ‖χ.toFun P * (Ideal.absNorm P : ℂ) ^ (-s)‖ := norm_sub_le _ _
            _ ≤ 1 + 1 * 1 := by
                rw [norm_one, norm_mul]
                gcongr
                exact hnorm P
            _ = 2 := by norm_num
      _ = 2 ^ hBf.toFinset.card := by simp
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hcard

/-- Two Hecke characters of the same modulus with the same values have the same `L`-series. -/
lemma heckeLSeries_congr {𝔤 : Ideal (𝓞 K)} (χ₁ χ₂ : HeckeChar K 𝔤) (h : ∀ I, χ₁.toFun I = χ₂.toFun I)
    (s : ℂ) : χ₁.LSeries s = χ₂.LSeries s := by
  unfold HeckeChar.LSeries HeckeChar.coeff
  simp_rw [h]

end Gen

theorem coreW (F : Type) [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (hK : ∀ w : InfinitePlace F, w.IsComplex) (ι : F →+* ℂ) :
    ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd (Ideal.absNorm (Ideal.span {(6 : 𝓞 F)})) 𝔪 →
      (∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal →
        ∃ p : SInt 𝔪, Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) →
      ∀ η : HeckeChar F 𝔪, ∃ A : ℝ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
        ∀ (u : SInt 𝔪) (𝔲 : Ideal (𝓞 F)), IsExterior 𝔪 𝔲 → IsSixthPowerFree 𝔲 → 𝔲 ≠ ⊤ →
          Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪)) → (∀ b : F, b ^ 6 ≠ (u : F)) →
          ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
            (∀ ξ : ℂ, 1 < ξ.re → Λ ξ = twistedL ι η u ξ) ∧
            ∀ ξ : ℂ, 3 / 1000 ≤ ξ.re → ξ.re ≤ 4 →
              ‖Λ ξ‖ ≤ C * (Ideal.absNorm 𝔲 : ℝ) ^ (1 / 2 + ε) * (2 + |ξ.im|) ^ A := by
  classical
  intro 𝔪 h𝔪 hsmall hprin η
  have hsix : ∀ v : HeightOneSpectrum (𝓞 F), (6 : 𝓞 F) ∈ v.asIdeal → 𝔪 ≤ v.asIdeal := by
    intro v hv
    refine hsmall v.asIdeal v.isPrime v.ne_bot (Nat.le_of_dvd ?_ ?_)
    · refine Nat.pos_of_ne_zero ?_
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      intro h0; have := congrArg (fun x : 𝓞 F => (x : F)) h0; simp at this
    · exact Ideal.absNorm_dvd_absNorm_of_le (by rwa [Ideal.span_singleton_le_iff_mem])
  refine ⟨3 * (nrComplexPlaces F : ℝ), fun ε hε => ?_⟩
  set δ := min ε (1 / 4)
  have hδ0 : 0 < δ := lt_min hε (by norm_num)
  have hδ1 : δ < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  obtain ⟨C0, hC0, hconv⟩ := abs_convexity F hδ0 hδ1
  set dK : ℝ := |(discr F : ℝ)|
  set K1 : ℝ := (Ideal.absNorm 𝔪 : ℝ) * ((Ideal.absNorm (D6 F) : ℝ) * (Ideal.absNorm 𝔪 : ℝ))
  set E0 : ℝ := 2 ^ (C3A.finite_primes_ge h𝔪).toFinset.card
  refine ⟨C0 * (dK * K1) ^ (1 / 2 + δ) * E0, fun u 𝔲 hext hfree htop hgen hnon => ?_⟩
  have h : BridgeHyp 𝔪 u 𝔲 := ⟨h𝔪, hsix, hprin, hgen, hfree, hnon⟩
  set ψ := psi F hζ ι (uUnit h)
  set 𝔠 := ArtinL.Abelian.conductor ψ
  set 𝔤 := 𝔪 * 𝔠
  have h𝔤 : 𝔤 ≠ ⊥ := mul_ne_zero h𝔪 (ArtinL.Abelian.conductor_ne_bot ψ)
  set ωH := omegaH hζ ι hK h η
  set ω := T12A.rayChar ωH
  obtain ⟨𝔣, h𝔤𝔣, χ₀, hχ₀, hD, hprim⟩ := exists_primitive hK h𝔤 ω
  have h𝔣 : 𝔣 ≠ ⊥ := fun h0 => h𝔤 (eq_bot_iff.2 (h0 ▸ h𝔤𝔣))
  -- every exterior prime over `𝔲` divides `𝔣`
  have hA : ∀ P₀ : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ P₀.asIdeal → 𝔲 ≤ P₀.asIdeal →
      P₀.asIdeal ∣ 𝔣 := by
    intro P₀ hm hu
    obtain ⟨𝔠', -, ⟨k, hk⟩, β, hβ0, hc, hβ1, hne⟩ := exists_witness hζ ι hK h η P₀ hm hu
    by_contra hnot
    apply hne
    have hcop : IsCoprime 𝔣 (P₀.asIdeal ^ k) := by
      apply IsCoprime.pow_right
      rw [Ideal.isCoprime_iff_sup_eq, sup_comm]
      exact sup_top_of_not_le P₀.isMaximal (fun hle => hnot (Ideal.dvd_iff_le.2 hle))
    have hdvd : 𝔣 ∣ (𝔪 * 𝔠') * P₀.asIdeal ^ k := by
      have : 𝔤 = (𝔪 * 𝔠') * P₀.asIdeal ^ k := by
        have hk' : 𝔠 = P₀.asIdeal ^ k * 𝔠' := hk
        show 𝔪 * 𝔠 = _; rw [hk']; ring
      rw [← this]; exact Ideal.dvd_iff_le.2 h𝔤𝔣
    have h2 := hcop.dvd_of_dvd_mul_right hdvd
    exact hD β hβ0 hc (Ideal.le_of_dvd h2 hβ1)
  -- `χ₀ ≠ 1`
  have hχ₀1 : χ₀ ≠ 1 := by
    intro h1
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ htop
    have hP0 : P ≠ ⊥ := fun h0 => hext.1 (eq_bot_iff.2 (h0 ▸ hle))
    let P₀ : HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime, hP0⟩
    have hm : ¬ 𝔪 ≤ P₀.asIdeal := by
      intro hm; apply hP.ne_top; rw [eq_top_iff, ← hext.2]; exact sup_le hle hm
    obtain ⟨-, -, -, β, hβ0, hc, -, hne⟩ := exists_witness hζ ι hK h η P₀ hm hle
    apply hne
    rw [← hχ₀, h1, MonoidHom.one_apply]
  -- analytic input
  set D : ℝ := dK * (Ideal.absNorm 𝔣 : ℝ)
  have hdK1 : (1 : ℝ) ≤ dK := by
    have h0 := NumberField.discr_ne_zero F
    have : (1 : ℤ) ≤ |discr F| := Int.one_le_abs h0
    have e : dK = ((|discr F| : ℤ) : ℝ) := by simp [dK]
    rw [e]; exact_mod_cast this
  have hN𝔣 : (1 : ℝ) ≤ Ideal.absNorm 𝔣 := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have hD1 : 1 ≤ D := by nlinarith
  obtain ⟨L, hL, hLre, hLb⟩ := hconv 𝔣 h𝔣 (rayH hK χ₀) D hD1
    (feHyp_rayH hK h𝔣 χ₀ hχ₀1 hprim) (growthH_rayH hK h𝔣 χ₀ hχ₀1 δ)
  -- the Euler factors
  obtain ⟨-, -, -, χ'', hagree, hLrel⟩ :=
    heckeLSeries_euler_package_of_le F 𝔣 𝔤 h𝔤 h𝔤𝔣 (rayH hK χ₀)
  have hχ'' : ∀ I, χ''.toFun I = ωH.toFun I := by
    intro I
    by_cases hI : I ≠ ⊥ ∧ I ⊔ 𝔤 = ⊤
    · rw [hagree I hI.2]
      have hI𝔣 : I ≠ ⊥ ∧ I ⊔ 𝔣 = ⊤ := ⟨hI.1, by rw [eq_top_iff, ← hI.2]; exact sup_le_sup_left h𝔤𝔣 _⟩
      show (if _ then _ else _) = _
      rw [if_pos hI𝔣, T12A.heckeChar_eq_ite ωH I, if_pos hI, ← hχ₀, T12A.cls, T12A.cls, dif_pos hI,
        dif_pos hI𝔣, piMap_mk]
    · rw [(χ''.eq_zero_iff' I).2 (by tauto), (ωH.eq_zero_iff' I).2 (by tauto)]
  set B : Set (Ideal (𝓞 F)) := {P | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔤 ≤ P ∧ P ⊔ 𝔣 = ⊤}
  have hB : B ⊆ {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P} := by
    rintro P ⟨hP, hP0, hle, htopP⟩
    refine ⟨hP, hP0, ?_⟩
    rcases hP.mul_le.1 hle with h1 | h1
    · exact h1
    · by_contra hm
      set v : HeightOneSpectrum (𝓞 F) := ⟨P, hP, hP0⟩
      have hram : ¬ ArtinL.Abelian.IsUnramifiedAt ψ v :=
        (ArtinL.Abelian.dvd_conductor_iff_not_isUnramifiedAt F _ ψ v).1 (Ideal.dvd_iff_le.2 h1)
      have hu : 𝔲 ≤ P := by
        by_contra hc; exact hram (localValue_eq_sextic hζ ι h hm hc).1
      exact (sup_eq_top_iff_not_dvd v 𝔣).1 htopP (hA v hm hu)
  obtain ⟨hEd, hEb⟩ := efac_generic h𝔣 h𝔪 (rayH hK χ₀) B hB
  set E : ℂ → ℂ := fun s => ∏ᶠ P ∈ B, (1 - (rayH hK χ₀).toFun P * (Ideal.absNorm P : ℂ) ^ (-s))
  have hrel : ∀ s : ℂ, 1 < s.re → ωH.LSeries s = (rayH hK χ₀).LSeries s * E s := by
    intro s hs
    have h1 := hLrel s hs
    simp_rw [finprod_inv_distrib] at h1
    change (rayH hK χ₀).LSeries s = χ''.LSeries s * (E s)⁻¹ at h1
    have hne := (C3A.euler1 (rayH hK χ₀) s (T12A.norm_heckeChar_le h𝔣 _) hs).2
    have hE : E s ≠ 0 := by
      intro h0; rw [h0, inv_zero, mul_zero] at h1; exact hne h1
    rw [← heckeLSeries_congr χ'' ωH hχ'' s, h1, mul_assoc, inv_mul_cancel₀ hE, mul_one]
  refine ⟨fun ξ => L ξ * E ξ, hL.mul hEd, fun ξ hξ => ?_, fun ξ h1 h2 => ?_⟩
  · show L ξ * E ξ = _
    rw [twistedL_eq hζ ι hK h η hξ, hrel ξ hξ, hLre ξ hξ]
  -- the bound
  have hcond := absNorm_conductor_psi_le hζ ι (uUnit h) (𝔪 * 𝔲) (mul_ne_zero h𝔪 hext.1) (by
    intro v _ hval
    by_cases hvm : 𝔪 ≤ v.asIdeal
    · exact le_trans (Ideal.mul_le_left (I := 𝔪) (J := 𝔲)) hvm
    · by_cases hv𝔲 : 𝔲 ≤ v.asIdeal
      · exact le_trans (Ideal.mul_le_right (I := 𝔪) (J := 𝔲)) hv𝔲
      · exact absurd (val_eq_one v hvm hgen hv𝔲) hval)
  rw [map_mul] at hcond
  have hN𝔤 : Ideal.absNorm 𝔣 ≤ Ideal.absNorm 𝔤 :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]))
      (Ideal.absNorm_dvd_absNorm_of_le h𝔤𝔣)
  have hq : (1 : ℝ) ≤ Ideal.absNorm 𝔲 := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hext.1)
  have hN : D ≤ dK * K1 * Ideal.absNorm 𝔲 := by
    have h3 : (Ideal.absNorm 𝔣 : ℝ) ≤ K1 * Ideal.absNorm 𝔲 := by
      have : Ideal.absNorm 𝔣 ≤ Ideal.absNorm 𝔪 * (Ideal.absNorm (D6 F) * Ideal.absNorm 𝔪 *
          Ideal.absNorm 𝔲) := by
        calc Ideal.absNorm 𝔣 ≤ Ideal.absNorm 𝔤 := hN𝔤
          _ = Ideal.absNorm 𝔪 * Ideal.absNorm 𝔠 := map_mul _ _ _
          _ ≤ Ideal.absNorm 𝔪 * (Ideal.absNorm (D6 F) * (Ideal.absNorm 𝔪 * Ideal.absNorm 𝔲)) :=
            Nat.mul_le_mul_left _ hcond
          _ = _ := by ring
      simp only [K1]; push_cast
      calc (Ideal.absNorm 𝔣 : ℝ) ≤ ((Ideal.absNorm 𝔪 * (Ideal.absNorm (D6 F) * Ideal.absNorm 𝔪 *
          Ideal.absNorm 𝔲) : ℕ) : ℝ) := by exact_mod_cast this
        _ = _ := by push_cast; ring
    simp only [D]
    calc dK * (Ideal.absNorm 𝔣 : ℝ) ≤ dK * (K1 * Ideal.absNorm 𝔲) :=
          mul_le_mul_of_nonneg_left h3 (by linarith)
      _ = _ := by ring
  have hK1 : 0 ≤ dK * K1 := by positivity
  have hDp : D ^ (1 / 2 + δ) ≤ (dK * K1) ^ (1 / 2 + δ) * (Ideal.absNorm 𝔲 : ℝ) ^ (1 / 2 + ε) := by
    calc D ^ (1 / 2 + δ) ≤ (dK * K1 * Ideal.absNorm 𝔲) ^ (1 / 2 + δ) :=
          Real.rpow_le_rpow (by linarith) hN (by linarith)
      _ = (dK * K1) ^ (1 / 2 + δ) * (Ideal.absNorm 𝔲 : ℝ) ^ (1 / 2 + δ) :=
          Real.mul_rpow hK1 (by positivity)
      _ ≤ _ := by gcongr
  have hAexp : (1 + |ξ.im|) ^ (3 * (nrComplexPlaces F : ℝ)) ≤
      (2 + |ξ.im|) ^ (3 * (nrComplexPlaces F : ℝ)) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  have hb := hLb ξ (by linarith) h2
  have he := hEb ξ (by linarith)
  show ‖L ξ * E ξ‖ ≤ _
  rw [norm_mul]
  calc ‖L ξ‖ * ‖E ξ‖
      ≤ (C0 * D ^ (1 / 2 + δ) * (1 + |ξ.im|) ^ (3 * (nrComplexPlaces F : ℝ))) * E0 :=
        mul_le_mul hb he (norm_nonneg _) (by positivity)
    _ ≤ (C0 * ((dK * K1) ^ (1 / 2 + δ) * (Ideal.absNorm 𝔲 : ℝ) ^ (1 / 2 + ε)) *
          (2 + |ξ.im|) ^ (3 * (nrComplexPlaces F : ℝ))) * E0 := by gcongr
    _ = C0 * (dK * K1) ^ (1 / 2 + δ) * E0 * (Ideal.absNorm 𝔲 : ℝ) ^ (1 / 2 + ε) *
          (2 + |ξ.im|) ^ (3 * (nrComplexPlaces F : ℝ)) := by ring

end L3W

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_Core: (8.14) for a number field in `Type`

For `F : Type` totally complex with a primitive sixth root of unity: for every `u ∈ R` with
`u R = 𝔲 R`, `𝔲` sixth-power-free and `u ∉ F^{×6}`, `kummerL u` continues to an entire `Λ` with
`‖Λ(w)‖ ≤ C (N𝔲)^{1/2+ε} (2 + |Im w|)^{3 r₂}` on `.003 ≤ Re w ≤ 4`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace IsDedekindDomain ArtinPrimitiveRoots.L3K.KB

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_Freq: a nonprincipal frequency element is not a sixth power

* `span_freqElt`: `u R = 𝔲 R` for `u = freqElt g r`, `𝔲 = r.1.1`;
* `freqElt_ne_pow_six`: for `r ≠ principalFreq`, `u ∉ F^{×6}` (`𝔲 ≠ ⊤`: an exterior valuation of `u`
  lies in `1..5`; `𝔲 = ⊤`: `u = rep(ε) gen ⊤` with `gen ⊤ ∈ U_S^6` and `ε ≠ 1`). -/

set_option autoImplicit false

open NumberField IsDedekindDomain WithZero

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

lemma isUnit_rep (ε : SClass 𝔪) : IsUnit (SClass.rep ε) :=
  Units.isUnit _

lemma span_freqElt (g : AllowedGen ι 𝔪) (r : FreqClass 𝔪) :
    Ideal.span {freqElt g r} = r.1.1.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  rw [freqElt, Ideal.span_singleton_mul_left_unit (isUnit_rep r.2), g.span_gen _ r.1.2.1]

lemma rep_coe (ε : SClass 𝔪) :
    ((SClass.rep ε : SInt 𝔪) : F) =
      (((Function.surjInv QuotientGroup.mk_surjective ε : SUnit 𝔪) : Fˣ) : F) := rfl

theorem freqElt_ne_pow_six (g : AllowedGen ι 𝔪) (r : FreqClass 𝔪) (hr : r ≠ principalFreq 𝔪) :
    ∀ b : F, b ^ 6 ≠ (freqElt g r : F) := by
  classical
  intro b hb
  by_cases htop : r.1.1 = ⊤
  · -- `r.2 ≠ 1`
    have hε : r.2 ≠ 1 := by
      intro h1
      apply hr
      exact Prod.ext (Subtype.ext htop) h1
    obtain ⟨η, hη⟩ := g.gen_mul ⊤ ⊤ ⟨top_ne_bot, top_sup_eq _⟩ ⟨top_ne_bot, top_sup_eq _⟩
    rw [Ideal.top_mul] at hη
    have hG0 : (g.gen ⊤ : F) ≠ 0 := by
      intro h0
      have hs := g.span_gen ⊤ ⟨top_ne_bot, top_sup_eq _⟩
      have : (g.gen ⊤ : SInt 𝔪) = 0 := Subtype.ext h0
      rw [this, Ideal.span_singleton_eq_bot.2 rfl, Ideal.map_top] at hs
      exact bot_ne_top hs
    have hG : (g.gen ⊤ : F) * ((η : Fˣ) : F) ^ 6 = 1 := by
      have h2 : (g.gen ⊤ : F) * 1 = (g.gen ⊤ : F) * (((η : Fˣ) : F) ^ 6 * (g.gen ⊤ : F)) := by
        rw [mul_one]; nth_rewrite 1 [hη]; ring
      have := mul_left_cancel₀ hG0 h2
      linear_combination -this
    set w := Function.surjInv (QuotientGroup.mk_surjective
      (s := (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range)) r.2
    have hw : (w : SClass 𝔪) = r.2 := Function.surjInv_eq _ _
    have hu : (freqElt g r : F) = ((w : Fˣ) : F) * (g.gen r.1.1 : F) := by
      rw [freqElt, Subalgebra.coe_mul, rep_coe]
    rw [show r.1.1 = ⊤ from htop] at hu
    -- `w = (b η)^6`
    set c : F := b * ((η : Fˣ) : F)
    have hc : c ^ 6 = ((w : Fˣ) : F) := by
      rw [mul_pow, hb, hu]
      linear_combination ((w : Fˣ) : F) * hG
    have hc0 : c ≠ 0 := by
      intro h0; rw [h0, zero_pow (by norm_num)] at hc
      exact (w : Fˣ).ne_zero hc.symm
    have hcu : Units.mk0 c hc0 ∈ (placesOf 𝔪).unit F := by
      intro v hv
      have hw1 : v.valuation F ((w : Fˣ) : F) = 1 := w.2 v hv
      rw [← hc, map_pow] at hw1
      have hne : v.valuation F c ≠ 0 := by simpa using hc0
      show v.valuation F c = 1
      rw [← exp_log hne] at hw1 ⊢
      rw [← exp_nsmul, ← exp_zero, exp_inj] at hw1
      rw [← exp_zero, exp_inj]
      simp at hw1; omega
    have hmem : w ∈ (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range := by
      refine ⟨⟨Units.mk0 c hc0, hcu⟩, ?_⟩
      apply Subtype.ext; apply Units.ext
      simp [powMonoidHom_apply, hc]
    apply hε
    rw [← hw]
    exact (QuotientGroup.eq_one_iff w).2 hmem
  · -- an exterior prime dividing `𝔲`
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ htop
    have h𝔲0 : r.1.1 ≠ ⊥ := r.1.2.1.1
    have hP0 : P ≠ ⊥ := fun h0 => h𝔲0 (eq_bot_iff.2 (h0 ▸ hle))
    let v : HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime, hP0⟩
    have hvm : ¬ 𝔪 ≤ v.asIdeal := by
      intro hm
      apply hP.ne_top
      rw [eq_top_iff, ← r.1.2.1.2]
      exact sup_le hle hm
    have hne := val_ne_exp_six v hvm r.1.2.2 (span_freqElt g r) hle
    have hu0 : (freqElt g r : F) ≠ 0 := by
      intro h0
      have hs := span_freqElt g r
      have : freqElt g r = 0 := Subtype.ext h0
      rw [this, Ideal.span_singleton_eq_bot.2 rfl] at hs
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔲0
      have hxm : algebraMap (𝓞 F) (SInt 𝔪) x ∈ r.1.1.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
        Ideal.mem_map_of_mem _ hx
      rw [← hs, Ideal.mem_bot] at hxm
      apply hx0
      have := congrArg (fun z : SInt 𝔪 => (z : F)) hxm
      simpa using this
    have hb0 : b ≠ 0 := by
      rintro rfl; rw [zero_pow (by norm_num)] at hb; exact hu0 hb.symm
    have hvb : v.valuation F b ≠ 0 := by simpa using hb0
    apply hne (log (v.valuation F b))
    rw [← hb, map_pow, ← exp_log hvb, ← exp_nsmul, log_exp]
    congr 1

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # T12A_Prin: removing Euler factors from `ζ_K`

For a finite set `T` of primes and `Re s > 1`,
`∑_{I coprime to T} N(I)^{-s} = ∏_{v ∈ T} (1 - N(v)^{-s}) · ζ_K(s)`. -/

set_option maxHeartbeats 4000000
set_option autoImplicit false

open NumberField Complex Ideal IsDedekindDomain

namespace ArtinPrimitiveRoots.T12A

variable {K : Type*} [Field K] [NumberField K]

end ArtinPrimitiveRoots.T12A

end
end

section
section
/-! # T12A_Main: continuation of `HeckeChar.LSeries` (cut T1)

* nontrivial ray class character: entire, by 17728196 (`IsParity` with `S = ∅`);
* trivial: `L(s, χ) = ∏_{v ∣ 𝔪} (1 - N v^{-s}) · ζ_K(s)`, continued by 8087d96f;
* a field in an arbitrary universe is moved to `Type` along a ring isomorphism. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply Complex

namespace ArtinPrimitiveRoots

namespace T12A

section Principal

variable {K : Type} [Field K] [NumberField K] {𝔪 : Ideal (𝓞 K)}

end Principal

section Transport


theorem exists_small_model (F : Type u) [Field F] [NumberField F] :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : NumberField F₀), Nonempty (F₀ ≃+* F) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ F
  have hint : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  haveI : Fact (Irreducible (minpoly ℚ α)) := ⟨minpoly.irreducible hint⟩
  let e : AdjoinRoot (minpoly ℚ α) ≃ₐ[ℚ] F :=
    (IntermediateField.adjoinRootEquivAdjoin ℚ hint).trans
      ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv)
  haveI : FiniteDimensional ℚ (AdjoinRoot (minpoly ℚ α)) :=
    LinearEquiv.finiteDimensional e.toLinearEquiv.symm
  haveI : NumberField (AdjoinRoot (minpoly ℚ α)) := { }
  exact ⟨_, inferInstance, inferInstance, ⟨e.toRingEquiv⟩⟩

end Transport

end T12A

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3K_Main: KummerConvexity (8.14), statement verbatim, for `F : Type*`

Transport of `L3K.core` from a universe-0 model `F₀ ≃+* F` (T12A `exists_small_model`, C0R
transport lemmas). This module does not import the target's stub. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace IsDedekindDomain UniqueFactorizationMonoid

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

/-- A number field with a primitive sixth root of unity is totally complex. -/
lemma isComplex_of_prim6 (K : Type*) [Field K] [NumberField K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 6) (w : InfinitePlace K) : w.IsComplex := by
  rw [← not_isReal_iff_isComplex]
  intro hw
  have h := hζ.map_of_injective (embedding_of_isReal hw).injective
  have h6 : ((embedding_of_isReal hw) ζ) ^ 6 = 1 := h.pow_eq_one
  have h2 : ((embedding_of_isReal hw) ζ) ^ 2 = 1 := by
    have : (((embedding_of_isReal hw) ζ) ^ 2) ^ 3 = 1 := by rw [← pow_mul]; exact h6
    exact (pow_eq_one_iff_of_nonneg (sq_nonneg _) (by norm_num)).1 this
  have := h.dvd_of_pow_eq_one 2 h2
  omega

variable {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']

lemma rsMul (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)} (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (x : SInt 𝔪) :
    residueSymbol ι 𝔪 (I * J) x = residueSymbol ι 𝔪 I x * residueSymbol ι 𝔪 J x := by
  unfold residueSymbol
  rw [normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

lemma rsPrime (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)} {P : Ideal (𝓞 F)} (hP : Irreducible P)
    (x : SInt 𝔪) : residueSymbol ι 𝔪 P x = sexticResidueSymbol ι 𝔪 P x := by
  unfold residueSymbol
  rw [normalizedFactors_irreducible hP, normalize_eq]; simp

lemma rsTop (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)} (x : SInt 𝔪) : residueSymbol ι 𝔪 ⊤ x = 1 := by
  unfold residueSymbol
  rw [← Ideal.one_eq_top, normalizedFactors_one]; simp

lemma extMul {𝔪 I J : Ideal (𝓞 F)} :
    IsExterior 𝔪 (I * J) ↔ IsExterior 𝔪 I ∧ IsExterior 𝔪 J := by
  unfold IsExterior
  have hb : I * J ≠ ⊥ ↔ I ≠ ⊥ ∧ J ≠ ⊥ := by
    simp only [ne_eq, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
  rw [hb, C3A.sup_mul_eq_top_iff]; tauto

/-- Residue symbols of exterior ideals transport. -/
lemma residueSymbol_transport (e : F ≃+* F') (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F))
    (h6 : ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → P ⊔ Ideal.span {6} = ⊤)
    (x : SInt 𝔪) (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) :
    residueSymbol (ι.comp (e.symm : F' →+* F)) (𝔪.map (RingOfIntegers.mapRingEquiv e))
        (I.map (RingOfIntegers.mapRingEquiv e)) (C0R.sIntEquiv e 𝔪 x) =
      residueSymbol ι 𝔪 I x := by
  set eO := RingOfIntegers.mapRingEquiv e
  revert hI
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro hI; exact absurd rfl hI.1
  | h₂ y hy =>
    intro _
    rw [Ideal.isUnit_iff.1 hy, Ideal.map_top, rsTop, rsTop]
  | h₃ a p ha hp ih =>
    intro hI
    obtain ⟨hpE, haE⟩ := extMul.1 hI
    have hpm : (p.map eO) ≠ ⊥ := fun h0 =>
      hpE.1 ((Ideal.map_eq_bot_iff_of_injective eO.injective).1 h0)
    have ham : (a.map eO) ≠ ⊥ := fun h0 =>
      haE.1 ((Ideal.map_eq_bot_iff_of_injective eO.injective).1 h0)
    have hpP : p.IsPrime := (Ideal.prime_iff_isPrime hpE.1).1 hp
    have hpmP : (p.map eO).IsPrime := Ideal.map_isPrime_of_equiv eO
    rw [Ideal.map_mul, rsMul _ _ _ hpm ham, rsMul _ _ _ hpE.1 haE.1,
      ih haE, rsPrime _ ((Ideal.prime_iff_isPrime hpm).2 hpmP).irreducible,
      rsPrime _ hp.irreducible,
      C0R.sexticResidueSymbol_transport e ι 𝔪 p (h6 p hpP hpE)]

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3W_Dev: TwistedConvexity, under the target's own name (does not import its stub)

`P` = the rows with `𝔲 = ⊤` (finitely many: `U_S/U_S^6` is finite, 4956b3f7). -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace IsDedekindDomain UniqueFactorizationMonoid

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3W

variable {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']

/-- Transport of a Hecke character along `e : F ≃+* F'`. -/
def heckeTr (e : F ≃+* F') {𝔪 : Ideal (𝓞 F)} (η : HeckeChar F 𝔪) :
    HeckeChar F' (𝔪.map (RingOfIntegers.mapRingEquiv e)) where
  toFun J := η.toFun (J.map (RingOfIntegers.mapRingEquiv e).symm)
  map_mul' I J := by rw [Ideal.map_mul]; exact η.map_mul' _ _
  eq_zero_iff' J := by
    set eO := RingOfIntegers.mapRingEquiv e
    rw [η.eq_zero_iff']
    have hb : J.map eO.symm = ⊥ ↔ J = ⊥ := Ideal.map_eq_bot_iff_of_injective eO.symm.injective
    have ht : J.map eO.symm ⊔ 𝔪 = ⊤ ↔ J ⊔ 𝔪.map eO = ⊤ := by
      have e1 : (J ⊔ 𝔪.map eO).map eO.symm = J.map eO.symm ⊔ 𝔪 := by
        rw [Ideal.map_sup, C0R.map_equiv_symm_map]
      rw [← e1]
      constructor
      · intro h1
        have := congrArg (Ideal.map eO) h1
        rwa [Ideal.map_top, show ((J ⊔ 𝔪.map eO).map eO.symm).map eO = J ⊔ 𝔪.map eO by
          have := C0R.map_equiv_symm_map eO.symm (J ⊔ 𝔪.map eO); rwa [RingEquiv.symm_symm] at this]
          at this
      · intro h1; rw [h1, Ideal.map_top]
    rw [hb, ne_eq, ne_eq, ht]
  map_principal' α hα h1 := by
    set eO := RingOfIntegers.mapRingEquiv e
    rw [Ideal.map_span, Set.image_singleton]
    refine η.map_principal' (eO.symm α) (by simpa using hα) ?_
    have := (C0R.mem_map_equiv eO 𝔪 (α - 1)).1 h1
    simpa using this

lemma twistedL_transport (e : F ≃+* F') (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F))
    (h6 : ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → P ⊔ Ideal.span {6} = ⊤)
    (η : HeckeChar F 𝔪) (u : SInt 𝔪) (ξ : ℂ) :
    twistedL (ι.comp (e.symm : F' →+* F)) (heckeTr e η) (C0R.sIntEquiv e 𝔪 u) ξ =
      twistedL ι η u ξ := by
  set eO := RingOfIntegers.mapRingEquiv e
  have hback : (𝔪.map eO).map (RingOfIntegers.mapRingEquiv e.symm) = 𝔪 := by
    rw [C0R.mapRingEquiv_symm, C0R.map_equiv_symm_map]
  let σ : {I : Ideal (𝓞 F) // IsExterior 𝔪 I} ≃ {I : Ideal (𝓞 F') // IsExterior (𝔪.map eO) I} :=
    { toFun := fun I => ⟨I.1.map eO, C0R.isExterior_map e I.2⟩
      invFun := fun J => ⟨J.1.map (RingOfIntegers.mapRingEquiv e.symm), by
        have := C0R.isExterior_map e.symm J.2
        rwa [hback] at this⟩
      left_inv := fun I => Subtype.ext (by
        show (I.1.map eO).map (RingOfIntegers.mapRingEquiv e.symm) = I.1
        rw [C0R.mapRingEquiv_symm, C0R.map_equiv_symm_map])
      right_inv := fun J => Subtype.ext (by
        show (J.1.map (RingOfIntegers.mapRingEquiv e.symm)).map eO = J.1
        have := C0R.map_equiv_symm_map (RingOfIntegers.mapRingEquiv e.symm) J.1
        rwa [C0R.mapRingEquiv_symm, RingEquiv.symm_symm] at this) }
  unfold twistedL
  rw [← σ.tsum_eq]
  refine tsum_congr fun I => ?_
  show (heckeTr e η).toFun (I.1.map eO) * (starRingEnd ℂ) (residueSymbol _ _ (I.1.map eO) _) *
    (Ideal.absNorm (I.1.map eO) : ℂ) ^ (-ξ) = _
  rw [L3K.residueSymbol_transport e ι 𝔪 h6 u I.1 I.2, C0R.absNorm_map_equiv]
  show η.toFun ((I.1.map eO).map eO.symm) * _ * _ = _
  rw [C0R.map_equiv_symm_map]

lemma finite_placesOf' {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) : (placesOf 𝔪).Finite := by
  have hfin := C3A.finite_primes_ge h𝔪
  refine Set.Finite.of_finite_image (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) ?_
    (fun v _ w _ h => HeightOneSpectrum.ext h)
  refine hfin.subset ?_
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v.isPrime, v.ne_bot, hv⟩

theorem finite_sClass' {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) {ζ : F} (hζ6 : IsPrimitiveRoot ζ 6) :
    Finite (SClass 𝔪) := by
  haveI : Finite (placesOf 𝔪) := (finite_placesOf' h𝔪).to_subtype
  have hμ : (primitiveRoots 6 F).Nonempty := ⟨ζ, (mem_primitiveRoots (by norm_num)).2 hζ6⟩
  have hc := NumberField.natCard_sUnit_quotient_range_powMonoidHom F (placesOf 𝔪) hμ
  apply Nat.finite_of_card_ne_zero
  show Nat.card (↥((placesOf 𝔪).unit F) ⧸
    (powMonoidHom 6 : ↥((placesOf 𝔪).unit F) →* ↥((placesOf 𝔪).unit F)).range) ≠ 0
  rw [hc]
  positivity

end L3W

open L3K L3W in
theorem exists_cutoff_exists_differentiable_eq_twistedL_and_norm_le (n : ℕ) (hn0 : 0 < n)
    (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪), ∃ P : Finset (FreqClass 𝔪), ∃ A : ℝ,
        ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ r : FreqClass 𝔪, r ≠ principalFreq 𝔪 → r ∉ P →
          ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
            (∀ ξ : ℂ, 1 < ξ.re → Λ ξ = twistedL ι χ (freqElt g r) ξ) ∧
            ∀ ξ : ℂ, 3 / 1000 ≤ ξ.re → ξ.re ≤ 4 →
              ‖Λ ξ‖ ≤ C * (Ideal.absNorm r.1.1 : ℝ) ^ (1 / 2 + ε) * (2 + |ξ.im|) ^ A := by
  classical
  haveI : NeZero n := ⟨hn0.ne'⟩
  -- a primitive sixth root of unity
  have hζn := IsCyclotomicExtension.zeta_spec n ℚ F
  obtain ⟨k, hk⟩ := (show 6 ∣ n from dvd_trans (by norm_num) hn)
  have hζ6 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ k) 6 :=
    hζn.pow hn0 (by rw [hk]; ring)
  -- the universe-0 model
  obtain ⟨F₀, _, _, ⟨e₀⟩⟩ := T12A.exists_small_model F
  set e : F ≃+* F₀ := e₀.symm
  set eO := RingOfIntegers.mapRingEquiv e
  have hζ' := hζ6.map_of_injective e.injective
  have hK' := isComplex_of_prim6 F₀ hζ'
  have hcore := coreW F₀ hζ' hK' (ι.comp (e.symm : F₀ →+* F))
  refine ⟨Ideal.absNorm (Ideal.span {(6 : 𝓞 F₀)}), fun 𝔪 h𝔪 hsmall χ g => ?_⟩
  set 𝔪' := 𝔪.map eO
  have h𝔪' : 𝔪' ≠ ⊥ := fun h0 => h𝔪 ((Ideal.map_eq_bot_iff_of_injective eO.injective).1 h0)
  have hsmall' : SmallPrimesDvd (Ideal.absNorm (Ideal.span {(6 : 𝓞 F₀)})) 𝔪' :=
    C0R.smallPrimesDvd_map e hsmall
  -- exterior primes of `F` avoid `6`
  have h6 : ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → P ⊔ Ideal.span {6} = ⊤ := by
    intro P hP hE
    have hPm : (P.map eO).IsPrime := Ideal.map_isPrime_of_equiv eO
    have hEm := C0R.isExterior_map e hE
    have hmax : (P.map eO).IsMaximal := hPm.isMaximal hEm.1
    have h1 : P.map eO ⊔ Ideal.span {(6 : 𝓞 F₀)} = ⊤ := by
      by_contra hne
      have hle : Ideal.span {(6 : 𝓞 F₀)} ≤ P.map eO :=
        le_of_eq (hmax.eq_of_le hne le_sup_left).symm |>.trans' le_sup_right
      have hN : Ideal.absNorm (P.map eO) ≤ Ideal.absNorm (Ideal.span {(6 : 𝓞 F₀)}) := by
        refine Nat.le_of_dvd (Nat.pos_of_ne_zero ?_) (Ideal.absNorm_dvd_absNorm_of_le hle)
        rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
        intro h; have := congrArg (fun x : 𝓞 F₀ => (x : F₀)) h; simp at this
      have := hsmall' _ hPm hEm.1 hN
      apply hPm.ne_top
      rw [eq_top_iff, ← hEm.2]; exact sup_le le_rfl this
    have h2 : (P ⊔ Ideal.span {6}).map eO = ⊤ := by
      rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_ofNat]; exact h1
    rw [← C0R.map_equiv_symm_map eO (P ⊔ Ideal.span {6}), h2, Ideal.map_top]
  -- exterior primes of `F₀` are principal in `R₀`
  have hprin' : ∀ v : HeightOneSpectrum (𝓞 F₀), ¬ 𝔪' ≤ v.asIdeal →
      ∃ p : SInt 𝔪', Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F₀) (SInt 𝔪')) := by
    intro v hv
    set P := v.asIdeal.map eO.symm
    have hPP : P.map eO = v.asIdeal := by
      have := C0R.map_equiv_symm_map eO.symm v.asIdeal
      rwa [RingEquiv.symm_symm] at this
    have hP : P.IsPrime := Ideal.map_isPrime_of_equiv eO.symm
    have hP0 : P ≠ ⊥ := fun h0 => v.ne_bot (by rw [← hPP, h0, Ideal.map_bot])
    have hPm : ¬ 𝔪 ≤ P := fun hle => hv (by rw [← hPP]; exact (C0R.map_equiv_le_iff eO).2 hle)
    have hE : IsExterior 𝔪 P := ⟨hP0, by
      by_contra hne
      exact hPm (le_trans le_sup_right (le_of_eq ((hP.isMaximal hP0).eq_of_le hne le_sup_left).symm))⟩
    refine ⟨C0R.sIntEquiv e 𝔪 (g.gen P), ?_⟩
    have := congrArg (Ideal.map (C0R.sIntEquiv e 𝔪)) (g.span_gen P hE)
    rw [Ideal.map_span, Set.image_singleton, C0R.map_map_sIntEquiv, hPP] at this
    exact this
  -- the exceptional rows `𝔲 = ⊤`
  haveI := finite_sClass' h𝔪 hζ6
  have hPfin : {r : FreqClass 𝔪 | r.1.1 = ⊤}.Finite := by
    refine Set.Finite.of_finite_image (f := Prod.snd) (Set.toFinite _) ?_
    intro r hr s hs hrs
    exact Prod.ext (Subtype.ext (hr.trans hs.symm)) hrs
  refine ⟨hPfin.toFinset, ?_⟩
  obtain ⟨A, hA⟩ := hcore 𝔪' h𝔪' hsmall' hprin' (heckeTr e χ)
  refine ⟨A, fun ε hε => ?_⟩
  obtain ⟨C, hC⟩ := hA ε hε
  refine ⟨C, fun r hr hrP => ?_⟩
  have htop : r.1.1 ≠ ⊤ := fun h => hrP ((Set.Finite.mem_toFinset _).2 h)
  set u := freqElt g r
  set 𝔲 := r.1.1
  have hfree' : IsSixthPowerFree (𝔲.map eO) := by
    intro J hJ
    have hle : 𝔲 ≤ (J.map eO.symm) ^ 6 := by
      have h1 : 𝔲.map eO ≤ J ^ 6 := Ideal.le_of_dvd hJ
      have h2 := Ideal.map_mono (f := eO.symm) h1
      rwa [C0R.map_equiv_symm_map, Ideal.map_pow] at h2
    have hu := r.1.2.2 _ (Ideal.dvd_iff_le.2 hle)
    rw [Ideal.isUnit_iff] at hu ⊢
    have := congrArg (Ideal.map eO) hu
    rwa [Ideal.map_top, show (J.map eO.symm).map eO = J by
      have := C0R.map_equiv_symm_map eO.symm J; rwa [RingEquiv.symm_symm] at this] at this
  have hgen' : Ideal.span {C0R.sIntEquiv e 𝔪 u} =
      (𝔲.map eO).map (algebraMap (𝓞 F₀) (SInt 𝔪')) := by
    have := congrArg (Ideal.map (C0R.sIntEquiv e 𝔪)) (span_freqElt g r)
    rw [Ideal.map_span, Set.image_singleton, C0R.map_map_sIntEquiv] at this
    exact this
  have hnon' : ∀ b : F₀, b ^ 6 ≠ ((C0R.sIntEquiv e 𝔪 u : SInt 𝔪') : F₀) := by
    intro b hb
    apply freqElt_ne_pow_six g r hr (e.symm b)
    rw [← map_pow, hb, C0R.sIntEquiv_coe, RingEquiv.symm_apply_apply]
  have htop' : 𝔲.map eO ≠ ⊤ := fun h => htop (by
    have := congrArg (Ideal.map eO.symm) h
    rwa [C0R.map_equiv_symm_map, Ideal.map_top] at this)
  obtain ⟨Λ, hΛd, hΛeq, hΛb⟩ := hC _ _ (C0R.isExterior_map e r.1.2.1) hfree' htop' hgen' hnon'
  refine ⟨Λ, hΛd, fun ξ hξ => (hΛeq ξ hξ).trans (twistedL_transport e ι 𝔪 h6 χ u ξ),
    fun ξ h1 h2 => ?_⟩
  have := hΛb ξ h1 h2
  rwa [C0R.absNorm_map_equiv] at this

end ArtinPrimitiveRoots

end
end
end

section
open ArtinPrimitiveRoots

open NumberField

theorem solution (n : ℕ) (hn0 : 0 < n)
    (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪), ∃ P : Finset (FreqClass 𝔪), ∃ A : ℝ,
        ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ r : FreqClass 𝔪, r ≠ principalFreq 𝔪 → r ∉ P →
          ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
            (∀ ξ : ℂ, 1 < ξ.re → Λ ξ = twistedL ι χ (freqElt g r) ξ) ∧
            ∀ ξ : ℂ, 3 / 1000 ≤ ξ.re → ξ.re ≤ 4 →
              ‖Λ ξ‖ ≤ C * (Ideal.absNorm r.1.1 : ℝ) ^ (1 / 2 + ε) * (2 + |ξ.im|) ^ A := by
  exact ArtinPrimitiveRoots.exists_cutoff_exists_differentiable_eq_twistedL_and_norm_le n hn0 hn F ι

end
