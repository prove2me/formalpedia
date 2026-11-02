-- Prove2me | Definitions.Def_OAIQ098D004
-- name    : OAIQ098D004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:24:54.948206+00:00
-- url     : https://prove2.me/theorems/a79bd731-0d2f-436c-a404-65771d7741f3
-- title:
--   Definitions bundle OAIQ098D004 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 685 declarations of OpenAI's Lean: 595 definitions, 4 instances and 86 theorems. The definitions and types are `OAI.SharpPlanar.CachedData.tm0_100_0.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_100_1.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_12_0.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_12_1.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_13_0.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_13_1.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_15_0.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_15_1.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_16_0.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_16_1.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_19_0.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_19_1.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_1_0.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_1_1.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_21_0.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_21_1.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_24_0.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_24_1.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_25_0.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_25_1.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_27_0.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_27_1.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_28_0.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_28_1.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_31_0.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_31_1.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_33_0.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_33_1.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_36_0.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_36_1.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_37_0.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_37_1.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_39_0.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_39_1.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_3_0.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_3_1.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_40_0.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_40_1.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_43_0.realAnswer`, `OAI.SharpPlanar.CachedData.tm0_43_1.realAnswer` and 555 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_BasisIntervals`, `PlanarPacking_BasisQuadrature`, `PlanarPacking_Cardinal`, `PlanarPacking_Certificate_DEntries`, `PlanarPacking_Certificate_LEntries`, `PlanarPacking_Certificate_TableMoments1`, `PlanarPacking_Certificate_TableMoments100`, `PlanarPacking_Certificate_TableMoments12`, `PlanarPacking_Certificate_TableMoments13`, `PlanarPacking_Certificate_TableMoments15`, `PlanarPacking_Certificate_TableMoments16`, `PlanarPacking_Certificate_TableMoments19`, `PlanarPacking_Certificate_TableMoments21`, `PlanarPacking_Certificate_TableMoments24`, `PlanarPacking_Certificate_TableMoments25`, `PlanarPacking_Certificate_TableMoments27`, `PlanarPacking_Certificate_TableMoments28`, `PlanarPacking_Certificate_TableMoments3`, `PlanarPacking_Certificate_TableMoments31`, `PlanarPacking_Certificate_TableMoments33`, `PlanarPacking_Certificate_TableMoments36`, `PlanarPacking_Certificate_TableMoments37`, `PlanarPacking_Certificate_TableMoments39`, `PlanarPacking_Certificate_TableMoments4`, `PlanarPacking_Certificate_TableMoments40`, `PlanarPacking_Certificate_TableMoments43`, `PlanarPacking_Certificate_TableMoments45`, `PlanarPacking_Certificate_TableMoments48`, `PlanarPacking_Certificate_TableMoments49`, `PlanarPacking_Certificate_TableMoments51`, `PlanarPacking_Certificate_TableMoments52`, `PlanarPacking_Certificate_TableMoments55`, `PlanarPacking_Certificate_TableMoments57`, `PlanarPacking_Certificate_TableMoments60`, `PlanarPacking_Certificate_TableMoments61`, `PlanarPacking_Certificate_TableMoments63`, `PlanarPacking_Certificate_TableMoments64`, `PlanarPacking_Certificate_TableMoments67`, `PlanarPacking_Certificate_TableMoments69`, `PlanarPacking_Certificate_TableMoments7`, `PlanarPacking_Certificate_TableMoments72`, `PlanarPacking_Certificate_TableMoments73`, `PlanarPacking_Certificate_TableMoments75`, `PlanarPacking_Certificate_TableMoments76`, `PlanarPacking_Certificate_TableMoments79`, `PlanarPacking_Certificate_TableMoments81`, `PlanarPacking_Certificate_TableMoments84`, `PlanarPacking_Certificate_TableMoments85`, `PlanarPacking_Certificate_TableMoments87`, `PlanarPacking_Certificate_TableMoments88`, `PlanarPacking_Certificate_TableMoments9`, `PlanarPacking_Certificate_TableMoments91`, `PlanarPacking_Certificate_TableMoments93`, `PlanarPacking_Certificate_TableMoments96`, `PlanarPacking_Certificate_TableMoments97`, `PlanarPacking_Certificate_TableMoments99`, `PlanarPacking_Certificate_WCertificates`, `PlanarPacking_Certificate_WUCert12`, `PlanarPacking_Entries`, `PlanarPacking_Fejer`, `PlanarPacking_FiniteCoordinates`, `PlanarPacking_FiniteFull`, `PlanarPacking_Intervals`, `PlanarPacking_MatrixIntervals`, `PlanarPacking_NodeIntervals`, `PlanarPacking_Quadrature`, `PlanarPacking_Roots`.
--
--   **Imports.** It imports the bundles `OAIQ098D000` and `OAIQ098D001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098D010`, `OAIQ098D033`, `OAIQ098D041`, `OAIQ098D042`, `OAIQ098D086`, `OAIQ098D098`, `OAIQ098D099`, `OAIQ098D100`, `OAIQ098D101`, `OAIQ098D102`, `OAIQ098D103`, `OAIQ098D105`, `OAIQ098D112`, `OAIQ098D113`, `OAIQ098D116`, `OAIQ098D120`, `OAIQ098D121`, `OAIQ098D122`, `OAIQ098D124`, `OAIQ098D125`, `OAIQ098D127`, `OAIQ098D128`, `OAIQ098D129`, `OAIQ098D131`, `OAIQ098D132`, `OAIQ098D134`, `OAIQ098D136`, `OAIQ098D137`, `OAIQ098D156`, `OAIQ098D157`, `OAIQ098D158`, `OAIQ098D159`, `OAIQ098D161`, `OAIQ098D164`, `OAIQ098D167`, `OAIQ098D168`, `OAIQ098D169`, `OAIQ098D170`, `OAIQ098D172`, `OAIQ098D174`, `OAIQ098D175`, `OAIQ098D177`, `OAIQ098D180`, `OAIQ098D182`, `OAIQ098D184`, `OAIQ098D186`, `OAIQ098D187`, `OAIQ098D188`, `OAIQ098D190`, `OAIQ098D191`, `OAIQ098D192`, `OAIQ098D198`, `OAIQ098D199`, `OAIQ098D202`, `OAIQ098D203`, `OAIQ098D205`, `OAIQ098D206`, `OAIQ098D208`, `OAIQ098D212`, `OAIQ098D214`, `OAIQ098D215`, `OAIQ098D217`, `OAIQ098D219`, `OAIQ098D220`, `OAIQ098D221`, `OAIQ098D223`, `OAIQ098D225`, `OAIQ098D227`, `OAIQ098D228`, `OAIQ098D231`, `OAIQ098D242`, `OAIQ098D244`, `OAIQ098D247`, `OAIQ098D250`, `OAIQ098D254`, `OAIQ098D255`, `OAIQ098D256`, `OAIQ098D257`, `OAIQ098D258`, `OAIQ098D259` and `OAIQ098D260`; the statements `OAI.SharpPlanar.RBox.contains_of_abs`, `OAI.SharpPlanar.RBox.lower_lt`, `OAI.SharpPlanar.normalized_kernel` and `OAI.SharpPlanar.piece_hasDerivAt`; the proofs of `OAI.SharpPlanar.RBox.contains_of_abs`, `OAI.SharpPlanar.RBox.lower_lt`, `OAI.SharpPlanar.normalized_kernel` and `OAI.SharpPlanar.piece_hasDerivAt`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098D000
import Definitions.Def_OAIQ098D001

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

noncomputable def z (t : ℝ) : ℂ :=
  -(B : ℂ) / ((t : ℂ) + Complex.I * (h : ℂ)) - Complex.I * (h : ℂ)


noncomputable def kernelMoment (ell : ℕ) (s t : ℝ) : ℂ :=
  lambda t * (Complex.I * Real.pi * z t) ^ ell *
    Complex.exp (Complex.I * Real.pi * z t * s)


noncomputable def K (p : CardinalData) (ell : ℕ) (s : ℝ) : ℝ :=
  ((p.C : ℂ) * (Pcoeff 0 * kernelMoment ell s 0 +
    ∑ j ∈ Finset.Icc 1 6, 2 * Pcoeff j * kernelMoment ell s ((j : ℝ) / 6)) +
    ∑ j ∈ Finset.range 6,
      ∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
        density p j t * kernelMoment ell s t).re


noncomputable def Scoords (x : X) (ni : Node × Bool) : ℝ :=
  if ni.2 then
    (D ni.1.val * K (positiveData x) 0 ni.1.val - K (positiveData x) 1 ni.1.val) /
      Q ni.1.val
  else -K (positiveData x) 0 ni.1.val / Q ni.1.val

theorem z_im (t : ℝ) : (z t).im = h * (B / (t ^ 2 + h ^ 2) - 1) := by
  simp [z, Complex.div_im, Complex.normSq, pow_two]
  ring

theorem strict_damping {t : ℝ} (ht : |t| ≤ 1) : (26 : ℝ) / 435 ≤ (z t).im := by
  rw [z_im]
  have ht2 : t ^ 2 ≤ 1 := by
    have := sq_le_sq₀ (abs_nonneg t) (show (0 : ℝ) ≤ 1 by norm_num)
    simpa using this.mpr ht
  have hd : 0 < t ^ 2 + h ^ 2 := by unfold h; positivity
  have hb : (4 : ℝ) / 3 / ((29 : ℝ) / 25) ≤ B / (t ^ 2 + h ^ 2) := by
    apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4/3) hd
    change t ^ 2 + (2/5 : ℝ) ^ 2 ≤ 29/25
    linarith
  unfold h at *
  norm_num at hb ⊢
  linarith



theorem z_bound (t : ℝ) : ‖z t‖ ≤ B / h + h := by
  have hden : 0 < ‖(t : ℂ) + Complex.I * (h : ℂ)‖ :=
    h_pos.trans_le (imaginary_gaussian_denominator t)
  calc
    ‖z t‖ ≤ ‖-(B : ℂ) / ((t : ℂ) + Complex.I * (h : ℂ))‖ +
      ‖Complex.I * (h : ℂ)‖ := norm_sub_le _ _
    _ = B / ‖(t : ℂ) + Complex.I * (h : ℂ)‖ + h := by
      simp [Complex.norm_real, abs_of_pos B_pos, abs_of_pos h_pos]
    _ ≤ B / h + h := add_le_add
      (div_le_div_of_nonneg_left B_pos.le h_pos (imaginary_gaussian_denominator t)) le_rfl


theorem kernelMoment_bound (ell : ℕ) {s t : ℝ} (hs : 0 ≤ s) (ht : |t| ≤ 1) :
    ‖kernelMoment ell s t‖ ≤ (1 / (b*h)) * (Real.pi * (B/h+h))^ell *
      Real.exp (-kappa*s) := by
  have hex : ‖Complex.exp (Complex.I * Real.pi * z t * s)‖ ≤
      Real.exp (-kappa*s) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul, zero_sub,
      sub_zero, zero_add]
    have hd := strict_damping ht
    dsimp [kappa]
    nlinarith [mul_nonneg Real.pi_pos.le hs]
  unfold kernelMoment
  rw [norm_mul, norm_mul, norm_pow, norm_mul, norm_mul, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, one_mul]
  have hb' := b_pos
  have hh' := h_pos
  have hB' := B_pos
  have hl := lambda_bound t
  have hz := z_bound t
  gcongr


noncomputable def kernelEnvelope (ell : ℕ) (s : ℝ) : ℝ :=
  (1/(b*h)) * (Real.pi*(B/h+h))^ell * Real.exp (-kappa*s)

lemma kernelEnvelope_nonneg (ell : ℕ) (s : ℝ) : 0 ≤ kernelEnvelope ell s := by
  have := b_pos
  have := h_pos
  have := B_pos
  unfold kernelEnvelope
  positivity

lemma kernelMoment_bound' (ell : ℕ) {s t : ℝ} (hs : 0 ≤ s) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖kernelMoment ell s t‖ ≤ kernelEnvelope ell s := by
  apply kernelMoment_bound ell hs
  rw [abs_of_nonneg ht.1]
  exact ht.2

lemma atomic_bound (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ‖Pcoeff 0 * kernelMoment ell s 0 +
      ∑ j ∈ Finset.Icc 1 6, 2 * Pcoeff j * kernelMoment ell s ((j : ℝ)/6)‖ ≤
      25 * kernelEnvelope ell s := by
  have hzero : ‖Pcoeff 0 * kernelMoment ell s 0‖ ≤ 5 * kernelEnvelope ell s := by
    rw [norm_mul, Pcoeff_norm]
    apply mul_le_mul_of_nonneg_left (kernelMoment_bound' ell hs (by simp)) (by norm_num [coeffMass])
  have hsum : ‖∑ j ∈ Finset.Icc 1 6, 2 * Pcoeff j * kernelMoment ell s ((j : ℝ)/6)‖ ≤
      20 * kernelEnvelope ell s := by
    calc
      _ ≤ ∑ j ∈ Finset.Icc 1 6, ‖2 * Pcoeff j * kernelMoment ell s ((j : ℝ)/6)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.Icc 1 6, 2 * ‖Pcoeff j‖ * kernelEnvelope ell s := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul, norm_mul, Complex.norm_ofNat]
        gcongr
        apply kernelMoment_bound' ell hs
        have hju : (j : ℝ) ≤ 6 := by exact_mod_cast (Finset.mem_Icc.mp hj).2
        constructor
        · positivity
        · linarith
      _ = 20 * kernelEnvelope ell s := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, positive_coeff_mass]
        ring
  exact (norm_add_le _ _).trans (by linarith)

lemma integral_piece_bound (p : CardinalData) (ell j : ℕ) (hj : j < 6)
    {s : ℝ} (hs : 0 ≤ s) :
    ‖∫ t in (j : ℝ)/6..((j : ℝ)+1)/6, density p j t * kernelMoment ell s t‖ ≤
      densityBound * (|p.c₀| + |p.d₀| + ‖p.x‖) * kernelEnvelope ell s / 6 := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t => density p j t * kernelMoment ell s t)
    (a := (j : ℝ)/6) (b := ((j : ℝ)+1)/6)
    (C := densityBound * (|p.c₀| + |p.d₀| + ‖p.x‖) * kernelEnvelope ell s) ?_
  · convert hb using 1
    all_goals try with_reducible_and_instances rfl
    rw [show ((j : ℝ)+1)/6 - (j : ℝ)/6 = 1/6 by ring, abs_of_pos (by norm_num : (0 : ℝ) < 1/6)]
    ring
  · intro t ht
    have htr := piece_interval hj (Set.uIoc_subset_uIcc ht)
    rw [norm_mul]
    exact mul_le_mul (density_bound p j htr) (kernelMoment_bound' ell hs htr)
      (norm_nonneg _) (by have := densityBound_nonneg; positivity)


lemma K_bound (p : CardinalData) (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    |K p ell s| ≤
      (25 * |p.C| + densityBound * (|p.c₀| + |p.d₀| + ‖p.x‖)) * kernelEnvelope ell s := by
  have hatom : ‖(p.C : ℂ) * (Pcoeff 0 * kernelMoment ell s 0 +
      ∑ j ∈ Finset.Icc 1 6, 2 * Pcoeff j * kernelMoment ell s ((j : ℝ)/6))‖ ≤
      25 * |p.C| * kernelEnvelope ell s := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |p.C| * (25 * kernelEnvelope ell s) := by
        gcongr; exact atomic_bound ell hs
      _ = _ := by ring
  have hsum : ‖∑ j ∈ Finset.range 6,
      ∫ t in (j : ℝ)/6..((j : ℝ)+1)/6, density p j t * kernelMoment ell s t‖ ≤
      densityBound * (|p.c₀| + |p.d₀| + ‖p.x‖) * kernelEnvelope ell s := by
    calc
      _ ≤ ∑ j ∈ Finset.range 6,
        ‖∫ t in (j : ℝ)/6..((j : ℝ)+1)/6, density p j t * kernelMoment ell s t‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range 6,
        (densityBound * (|p.c₀| + |p.d₀| + ‖p.x‖) * kernelEnvelope ell s / 6) := by
        exact Finset.sum_le_sum fun j hj => integral_piece_bound p ell j (Finset.mem_range.mp hj) hs
      _ = _ := by simp; ring
  unfold K
  exact (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans (by nlinarith))


lemma continuous_z : Continuous z := by
  unfold z
  fun_prop (disch := intro t; exact denominator_ne t)

lemma continuous_kernelMoment (ell : ℕ) (s : ℝ) : Continuous (kernelMoment ell s) := by
  unfold kernelMoment
  exact (continuous_lambda.mul ((continuous_const.mul continuous_z).pow ell)).mul
    (Complex.continuous_exp.comp ((continuous_const.mul continuous_z).mul continuous_const))

lemma piece_integrable (p : CardinalData) (ell j : ℕ) (hj : j < 6) (s : ℝ) :
    IntervalIntegrable (fun t => density p j t * kernelMoment ell s t) volume
      ((j : ℝ)/6) (((j : ℝ)+1)/6) := by
  exact ((continuousOn_density p j).mul (continuous_kernelMoment ell s).continuousOn).mono
    (fun _ ht => piece_interval hj ht) |>.intervalIntegrable

lemma K_positive_add (x y : X) (ell : ℕ) (s : ℝ) :
    K (positiveData (x+y)) ell s = K (positiveData x) ell s + K (positiveData y) ell s := by
  have hp (j : ℕ) (hj : j < 6) :
      (∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
        density (positiveData (x+y)) j t * kernelMoment ell s t) =
      (∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
        density (positiveData x) j t * kernelMoment ell s t) +
      (∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
        density (positiveData y) j t * kernelMoment ell s t) := by
    rw [← intervalIntegral.integral_add (piece_integrable _ ell j hj s) (piece_integrable _ ell j hj s)]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [density_positive_add x y j (piece_interval hj ht), add_mul]
  unfold K
  simp only [positiveData, Complex.ofReal_zero, zero_mul, zero_add]
  rw [← Complex.add_re, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact hp j (Finset.mem_range.mp hj)

lemma K_positive_smul (r : ℝ) (x : X) (ell : ℕ) (s : ℝ) :
    K (positiveData (r • x)) ell s = r * K (positiveData x) ell s := by
  unfold K
  simp only [positiveData, Complex.ofReal_zero, zero_mul, zero_add]
  change (∑ j ∈ Finset.range 6, ∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
    density (positiveData (r • x)) j t * kernelMoment ell s t).re = _
  simp_rw [density_positive_smul, mul_assoc, intervalIntegral.integral_const_mul,
    ← Finset.mul_sum]
  simp [Complex.mul_re, positiveData]


lemma K_positive_bound (x : X) (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    |K (positiveData x) ell s| ≤ densityBound * ‖x‖ * kernelEnvelope ell s := by
  simpa [positiveData] using K_bound (positiveData x) ell hs

lemma Scoords_bound (x : X) (ni : Node × Bool) :
    |Scoords x ni| ≤ allNodeWeight * densityBound * ‖x‖ *
      (kernelEnvelope 0 ni.1.val + kernelEnvelope 1 ni.1.val) := by
  have he0 := kernelEnvelope_nonneg 0 (ni.1.val : ℝ)
  have he1 := kernelEnvelope_nonneg 1 (ni.1.val : ℝ)
  have hd := densityBound_nonneg
  have hx := norm_nonneg x
  have hq := Q_pos ni.1.val
  have hc0 := K_positive_bound x 0 (Nat.cast_nonneg ni.1.val)
  have hc1 := K_positive_bound x 1 (Nat.cast_nonneg ni.1.val)
  have hlocal : |Scoords x ni| ≤ nodeWeight ni.1.val * densityBound * ‖x‖ *
      (kernelEnvelope 0 ni.1.val + kernelEnvelope 1 ni.1.val) := by
    unfold Scoords nodeWeight
    split
    · rw [abs_div, abs_of_pos hq]
      calc
        _ ≤ (|D ni.1.val| * |K (positiveData x) 0 ni.1.val| +
          |K (positiveData x) 1 ni.1.val|) / Q ni.1.val := by
          apply div_le_div_of_nonneg_right _ hq.le
          exact (abs_sub _ _).trans (by rw [abs_mul])
        _ ≤ (|D ni.1.val| * (densityBound * ‖x‖ * kernelEnvelope 0 ni.1.val) +
          densityBound * ‖x‖ * kernelEnvelope 1 ni.1.val) / Q ni.1.val := by gcongr
        _ ≤ _ := by
          apply (div_le_iff₀ hq).mpr
          field_simp
          nlinarith [mul_nonneg (abs_nonneg (D ni.1.val))
            (mul_nonneg (mul_nonneg hd hx) he1), mul_nonneg (mul_nonneg hd hx) he0]
    · rw [abs_div, abs_neg, abs_of_pos hq]
      calc
        _ ≤ (densityBound * ‖x‖ * kernelEnvelope 0 ni.1.val) / Q ni.1.val := by gcongr
        _ ≤ _ := by
          apply (div_le_iff₀ hq).mpr
          field_simp
          nlinarith [mul_nonneg (abs_nonneg (D ni.1.val))
            (mul_nonneg (mul_nonneg hd hx) (add_nonneg he0 he1)),
            mul_nonneg (mul_nonneg hd hx) he1]
  exact hlocal.trans (by gcongr; exact nodeWeight_le ni.1)


lemma kernelEnvelope_summable (ell : ℕ) : Summable (fun n : Node => kernelEnvelope ell n.val) := by
  have hh := exp_nat_summable.comp_injective (i := fun n : Node => n.val) Subtype.val_injective
  exact hh.mul_left ((1/(b*h)) * (Real.pi*(B/h+h))^ell)

lemma pairEnvelope_summable : Summable (fun ni : Node × Bool =>
    kernelEnvelope 0 ni.1.val + kernelEnvelope 1 ni.1.val) := by
  apply (summable_prod_of_nonneg (fun ni =>
    add_nonneg (kernelEnvelope_nonneg _ _) (kernelEnvelope_nonneg _ _))).mpr
  constructor
  · intro n; exact Summable.of_finite
  · simpa only [tsum_bool] using
      ((kernelEnvelope_summable 0).add (kernelEnvelope_summable 1)).add
        ((kernelEnvelope_summable 0).add (kernelEnvelope_summable 1))

lemma Scoords_summable (x : X) : Summable (fun ni : Node × Bool => |Scoords x ni|) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun ni => Scoords_bound x ni)
  exact pairEnvelope_summable.mul_left (allNodeWeight * densityBound * ‖x‖)

lemma Scoords_mem (x : X) : Memℓp (Scoords x) 1 := by
  apply memℓp_gen
  simpa using Scoords_summable x

lemma Scoords_add (x y : X) (ni : Node × Bool) :
    Scoords (x+y) ni = Scoords x ni + Scoords y ni := by
  unfold Scoords
  split <;> simp only [K_positive_add] <;> ring

lemma Scoords_smul (r : ℝ) (x : X) (ni : Node × Bool) :
    Scoords (r • x) ni = r * Scoords x ni := by
  unfold Scoords
  split <;> simp only [K_positive_smul] <;> ring

noncomputable def Slinear : X →ₗ[ℝ] X where
  toFun x := ⟨Scoords x, Scoords_mem x⟩
  map_add' x y := lp.ext (funext fun ni => Scoords_add x y ni)
  map_smul' r x := lp.ext (funext fun ni => Scoords_smul r x ni)

noncomputable def Sbound : ℝ := allNodeWeight * densityBound *
  ∑' ni : Node × Bool, (kernelEnvelope 0 ni.1.val + kernelEnvelope 1 ni.1.val)

lemma Slinear_bound (x : X) : ‖Slinear x‖ ≤ Sbound * ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div_one, Real.norm_eq_abs]
  change (∑' ni : Node × Bool, |Scoords x ni|) ≤ _
  calc
    _ ≤ ∑' ni : Node × Bool, allNodeWeight * densityBound * ‖x‖ *
      (kernelEnvelope 0 ni.1.val + kernelEnvelope 1 ni.1.val) :=
      (Scoords_summable x).tsum_le_tsum (fun ni => Scoords_bound x ni)
        (pairEnvelope_summable.mul_left _)
    _ = Sbound * ‖x‖ := by rw [tsum_mul_left]; unfold Sbound; ring


noncomputable def S : X →L[ℝ] X := Slinear.mkContinuous Sbound Slinear_bound

lemma S_apply (x : X) (ni : Node × Bool) : S x ni = Scoords x ni := rfl

end SharpPlanar

namespace SharpPlanar
open Complex

noncomputable def complexZ (t : ℂ) : ℂ :=
  -(B:ℂ)/(t+Complex.I*(h:ℂ))-Complex.I*(h:ℂ)

lemma disk_z_bound {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) : ‖complexZ t‖ < 31/5 := by
  have hd := disk_denominator_lower hj ht
  have hm := norm_sub_le (-(B:ℂ)/(t+Complex.I*(h:ℂ))) (Complex.I*(h:ℂ))
  simp only [norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,norm_mul,
    Complex.norm_I,one_mul,abs_of_pos B_pos,abs_of_pos h_pos] at hm
  have hb : B/‖t+Complex.I*(h:ℂ)‖ ≤ (40:ℝ)/7 := by
    apply (div_le_iff₀ (by linarith : 0 < ‖t+Complex.I*(h:ℂ)‖)).mpr
    norm_num [B]
    linarith
  change ‖-(B:ℂ)/(t+Complex.I*(h:ℂ))-Complex.I*(h:ℂ)‖ < _
  norm_num [h] at hm hb ⊢
  linarith

lemma disk_z_imaginary {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    -(1402/17505:ℝ) ≤ (complexZ t).im := by
  let a : ℂ := (diskCenter j:ℂ)+Complex.I*(h:ℂ)
  let Δ : ℝ := Complex.normSq a-(1/6:ℝ)^2
  have hΔ : 0 < Δ := by
    have hh := (disk_delta_bounds hj).1
    change 167/1200 ≤ Δ at hh
    linarith
  have hΔ1 : Δ ≤ 389/400 := (disk_delta_bounds hj).2
  have hrec := reciprocal_disk_bound (a:=a) (u:=t+Complex.I*(h:ℂ))
    (by norm_num : (0:ℝ) ≤ 1/6) hΔ
    (by simpa [a] using ht) (disk_denominator_ne hj ht)
  have hi := (le_abs_self _).trans ((Complex.abs_im_le_norm
    ((t+Complex.I*(h:ℂ))⁻¹-((Δ⁻¹:ℝ):ℂ)*conj a)).trans hrec)
  have haim : a.im = h := by simp [a]
  simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.conj_im,zero_mul,add_zero,haim] at hi
  change (t+Complex.I*(h:ℂ))⁻¹.im-Δ⁻¹*(-h) ≤ (1/6)/Δ at hi
  have htop : (t+Complex.I*(h:ℂ))⁻¹.im ≤ ((1/6:ℝ)-h)/Δ := by
    rw [div_eq_mul_inv] at hi ⊢
    nlinarith only [hi]
  have heq : (complexZ t).im = -B*(t+Complex.I*(h:ℂ))⁻¹.im-h := by
    simp [complexZ,div_eq_mul_inv,Complex.mul_im]
  rw [heq]
  have hb := mul_le_mul_of_nonpos_left htop (neg_nonpos.mpr B_pos.le)
  have hq : -(1402/17505:ℝ) ≤ -B*((1/6-h)/Δ)-h := by
    have hh : (-(1402/17505:ℝ)+h)*Δ ≤ -B*(1/6-h) := by
      norm_num [B,h] at *
      nlinarith
    have hh' := (le_div_iff₀ hΔ).mpr hh
    linear_combination hh'
  linarith

lemma disk_z_imaginary_simple {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    -(81/1000:ℝ) < (complexZ t).im := by
  have hh := disk_z_imaginary hj ht
  linarith

end SharpPlanar

namespace SharpPlanar
open Complex

noncomputable def complexTransformedFactor (m y : ℝ) (ell : ℕ) (t : ℂ) : ℂ :=
  complexLambda t * Complex.exp (Complex.I*Real.pi*complexZ t*m) *
    (Complex.I*Real.pi*complexZ t*y)^ell / (ell.factorial:ℂ)

lemma complexTransformedFactor_disk_bound {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) {m y : ℝ}
    (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖complexTransformedFactor m y ell t‖ ≤ 5*Real.exp (Real.pi*(87/5)) := by
  have htn := (disk_z_bound hj ht).le
  have hti := (disk_z_imaginary_simple hj ht).le
  have he : ‖Complex.exp (Complex.I*Real.pi*complexZ t*m)‖ ≤ Real.exp (Real.pi*(81/10)) := by
    refine (phase_exp_norm_bound hm0 hti).trans ?_
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hp : ‖(Complex.I*Real.pi*complexZ t*y)^ell/(ell.factorial:ℂ)‖ ≤
      Real.exp (Real.pi*(93/10)) := by
    refine (divided_power_norm _ ell).trans (Real.exp_le_exp.mpr ?_)
    simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    have hh := mul_le_mul htn hy (abs_nonneg y) (by norm_num : (0:ℝ) ≤ 31/5)
    nlinarith [Real.pi_pos]
  rw [complexTransformedFactor,mul_div_assoc,norm_mul,norm_mul]
  calc
    _ ≤ (5*Real.exp (Real.pi*(81/10)))*Real.exp (Real.pi*(93/10)) :=
      mul_le_mul (mul_le_mul (disk_lambda_bound hj ht).le he (norm_nonneg _)
        (by norm_num)) hp (norm_nonneg _) (by positivity)
    _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; ring

lemma transformedIntegrand_disk_bound (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {j : ℕ} (hj : j < 6) {t : ℂ} (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6)
    {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖finiteDensity c d j t * complexTransformedFactor m y ell t‖ ≤ (10:ℝ)^53 := by
  rw [norm_mul]
  calc
    _ ≤ (1000*Real.exp (100*Real.pi/6))*(5*Real.exp (Real.pi*(87/5))) :=
      mul_le_mul (finiteDensity_disk_bound c d hw hj ht)
        (complexTransformedFactor_disk_bound hj ht hm0 hm1 hy ell) (norm_nonneg _) (by positivity)
    _ = 5000*Real.exp ((100*Real.pi/6)+Real.pi*(87/5)) := by rw [Real.exp_add]; ring
    _ ≤ 5000*Real.exp 111 := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
      have hp := Real.pi_lt_d4
      linarith
    _ ≤ _ := numerical_moment_bound.le

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar
namespace IntegerIntervals

def RBox.Contains (a : RBox) (x : ℝ) : Prop :=
  (a.lo:ℝ) ≤ precision*x ∧ precision*x ≤ (a.hi:ℝ)

def mulLo (a b : RBox) : ℤ :=
  min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi))
def mulHi (a b : RBox) : ℤ :=
  max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))

def RBox.AddCheck (a b c : RBox) : Prop := c.lo ≤ a.lo+b.lo ∧ a.hi+b.hi ≤ c.hi
instance instDecidableAddCheck (a b c : RBox) : Decidable (a.AddCheck b c) := inferInstanceAs (Decidable (_ ∧ _))
def RBox.MulCheck (a b c : RBox) : Prop := c.lo*precision ≤ mulLo a b ∧ mulHi a b ≤ c.hi*precision

lemma mul_bounds {a b : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (mulLo a b:ℝ) ≤ (precision:ℝ)^2*(x*y) ∧
      (precision:ℝ)^2*(x*y) ≤ (mulHi a b:ℝ) := by
  convert real_mul_bounds hx hy using 1 <;> first | (with_reducible_and_instances rfl) | (push_cast [mulLo,mulHi] <;> ring_nf)

lemma RBox.add_contains {a b c : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y)
    (hc : a.AddCheck b c) : c.Contains (x+y) := by
  have h₁ : (c.lo:ℝ) ≤ a.lo+b.lo := by exact_mod_cast hc.1
  have h₂ : (a.hi:ℝ)+b.hi ≤ c.hi := by exact_mod_cast hc.2
  constructor <;> nlinarith only [hx.1,hx.2,hy.1,hy.2,h₁,h₂]

lemma RBox.mul_contains {a b c : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y)
    (hc : a.MulCheck b c) : c.Contains (x*y) := by
  have hh := mul_bounds hx hy
  have h₁ : (c.lo:ℝ)*precision ≤ mulLo a b := by exact_mod_cast hc.1
  have h₂ : (mulHi a b:ℝ) ≤ c.hi*precision := by exact_mod_cast hc.2
  constructor
  · exact (mul_le_mul_iff_right₀ precision_pos).mp (by nlinarith only [hh.1,h₁])
  · exact (mul_le_mul_iff_right₀ precision_pos).mp (by nlinarith only [hh.2,h₂])


def RBox.RatCheck (a : RBox) (m n : ℤ) : Prop :=
  0 < n ∧ a.lo*n ≤ precision*m ∧ precision*m ≤ a.hi*n
instance instDecidableRatCheck (a : RBox) (m n : ℤ) : Decidable (a.RatCheck m n) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
lemma RBox.rat_contains {a : RBox} {m n : ℤ} (h : a.RatCheck m n) :
    a.Contains ((m:ℝ)/n) := by
  have hn : (0:ℝ) < n := by exact_mod_cast h.1
  have h₁ : (a.lo:ℝ)*n ≤ precision*m := by exact_mod_cast h.2.1
  have h₂ : (precision:ℝ)*m ≤ a.hi*n := by exact_mod_cast h.2.2
  constructor
  · rw [← mul_div_assoc]; exact (le_div_iff₀ hn).mpr h₁
  · rw [← mul_div_assoc]; exact (div_le_iff₀ hn).mpr h₂

def RBox.neg (a : RBox) : RBox := ⟨-a.hi,-a.lo⟩
lemma RBox.neg_contains {a : RBox} {x : ℝ} (hx : a.Contains x) : a.neg.Contains (-x) := by
  simpa [Contains,neg,mul_neg] using And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)

def RBox.ScaleCheck (a c : RBox) (m n : ℤ) : Prop :=
  0 < n ∧ c.lo*n ≤ min (m*a.lo) (m*a.hi) ∧ max (m*a.lo) (m*a.hi) ≤ c.hi*n
instance instDecidableScaleCheck (a c : RBox) (m n : ℤ) : Decidable (a.ScaleCheck c m n) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

lemma RBox.scale_contains {a c : RBox} {x : ℝ} {m n : ℤ} (hx : a.Contains x)
    (hc : a.ScaleCheck c m n) : c.Contains (((m:ℝ)/n)*x) := by
  have hn : (0:ℝ) < n := by exact_mod_cast hc.1
  have h₁ : (c.lo:ℝ)*n ≤ min ((m:ℝ)*a.lo) ((m:ℝ)*a.hi) := by exact_mod_cast hc.2.1
  have h₂ : max ((m:ℝ)*a.lo) ((m:ℝ)*a.hi) ≤ (c.hi:ℝ)*n := by exact_mod_cast hc.2.2
  have hh : min ((m:ℝ)*a.lo) ((m:ℝ)*a.hi) ≤ (m:ℝ)*(precision*x) ∧
      (m:ℝ)*(precision*x) ≤ max ((m:ℝ)*a.lo) ((m:ℝ)*a.hi) := by
    apply between_mul hx <;> simp
  constructor
  · apply (mul_le_mul_iff_right₀ hn).mp
    convert h₁.trans hh.1 using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)
  · apply (mul_le_mul_iff_right₀ hn).mp
    convert hh.2.trans h₂ using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)

def RBox.InvCheck (a c : RBox) : Prop :=
  0 < a.lo ∧ 0 ≤ c.lo ∧ 0 ≤ c.hi ∧ c.lo*a.hi ≤ precision^2 ∧ precision^2 ≤ c.hi*a.lo
instance instDecidableInvCheck (a c : RBox) : Decidable (a.InvCheck c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))
lemma RBox.inv_contains {a c : RBox} {x : ℝ} (hx : a.Contains x)
    (hc : a.InvCheck c) : c.Contains x⁻¹ := by
  have ha : (0:ℝ) < a.lo := by exact_mod_cast hc.1
  have hcl : (0:ℝ) ≤ c.lo := by exact_mod_cast hc.2.1
  have hcu : (0:ℝ) ≤ c.hi := by exact_mod_cast hc.2.2.1
  have h₁ : (c.lo:ℝ)*a.hi ≤ (precision:ℝ)^2 := by exact_mod_cast hc.2.2.2.1
  have h₂ : (precision:ℝ)^2 ≤ (c.hi:ℝ)*a.lo := by exact_mod_cast hc.2.2.2.2
  have hp := precision_pos
  have hx0 : 0 < x := by nlinarith only [hx.1,ha,hp]
  constructor <;> rw [← div_eq_mul_inv]
  · apply (le_div_iff₀ hx0).mpr
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith only [mul_le_mul_of_nonneg_left hx.2 hcl,h₁]
  · apply (div_le_iff₀ hx0).mpr
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith only [mul_le_mul_of_nonneg_left hx.1 hcu,h₂]


def RBox.bound (a : RBox) : ℤ := max |a.lo| |a.hi|
lemma RBox.abs_bound {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (precision:ℝ)*|x| ≤ (a.bound:ℝ) := by
  rw [← abs_of_pos precision_pos,← abs_mul,abs_le]
  have h₁ : -(a.bound:ℝ) ≤ (a.lo:ℝ) := by
    have hh := (neg_abs_le a.lo).trans (le_refl a.lo)
    have hu : |a.lo| ≤ a.bound := le_max_left _ _
    exact_mod_cast (neg_le_neg hu).trans hh
  have h₂ : (a.hi:ℝ) ≤ (a.bound:ℝ) := by
    exact_mod_cast (le_abs_self a.hi).trans (le_max_right |a.lo| |a.hi|)
  exact ⟨h₁.trans hx.1,hx.2.trans h₂⟩

def piBounds : RBox := ⟨3141592653589793238460000000000,3141592653589793238470000000000⟩
lemma piBounds_contains : piBounds.Contains Real.pi := by
  have hp := Real.pi_gt_d20
  have hq := Real.pi_lt_d20
  norm_num [piBounds,RBox.Contains,precision]
  constructor <;> linarith

def bBounds : RBox := ⟨866025403784438646760000000000,866025403784438646770000000000⟩
lemma bBounds_contains : bBounds.Contains (Real.sqrt 3/2) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3:ℝ)
  norm_num [bBounds,RBox.Contains,precision]
  constructor <;> nlinarith

end IntegerIntervals
end SharpPlanar

namespace SharpPlanar.IntegerIntervals

def RBox.rat (m n : ℤ) : RBox := ⟨precision*m/n,-((-precision*m)/n)⟩
def RBox.mul (a b : RBox) : RBox :=
  ⟨mulLo a b/precision,-((-mulHi a b)/precision)⟩
def RBox.inv (a : RBox) : RBox := ⟨precision^2/a.hi,-((-precision^2)/a.lo)⟩

lemma RBox.rat_check (m n : ℤ) (hn : 0 < n) : (RBox.rat m n).RatCheck m n := by
  exact ⟨hn,floor_mul_le _ hn,by simpa only [RBox.rat, neg_mul] using le_ceil_mul (precision*m) hn⟩
lemma RBox.add_check (a b : RBox) : a.AddCheck b (a.add b) := ⟨le_rfl,le_rfl⟩
lemma RBox.mul_check (a b : RBox) : a.MulCheck b (a.mul b) :=
  ⟨floor_mul_le _ (by norm_num [precision]),le_ceil_mul _ (by norm_num [precision])⟩
lemma RBox.scale_check (a : RBox) (m n : ℤ) (hn : 0 < n) : a.ScaleCheck (a.scale m n) m n :=
  ⟨hn,floor_mul_le _ hn,le_ceil_mul _ hn⟩

lemma RBox.contains_rat (m n : ℤ) (hn : 0 < n) : (RBox.rat m n).Contains ((m:ℝ)/n) :=
  RBox.rat_contains (RBox.rat_check m n hn)
lemma RBox.contains_add {a b : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.add b).Contains (x+y) := RBox.add_contains hx hy (RBox.add_check _ _)
lemma RBox.contains_mul {a b : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.mul b).Contains (x*y) := RBox.mul_contains hx hy (RBox.mul_check _ _)
lemma RBox.contains_scale {a : RBox} {x : ℝ} (hx : a.Contains x) (m n : ℤ) (hn : 0 < n) :
    (a.scale m n).Contains (((m:ℝ)/n)*x) := RBox.scale_contains hx (RBox.scale_check _ _ _ hn)

end SharpPlanar.IntegerIntervals

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Roots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Certified roots of unity

Integer enclosures for the 1024th roots of unity, obtained from a certified
Taylor approximation and repeated squaring.
-/

namespace SharpPlanar

lemma rootPhase_add (n m : ℕ) : rootPhase (n+m) = rootPhase n*rootPhase m := by
  unfold rootPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma rootPhase_periodic (n : ℕ) : rootPhase (n+1024) = rootPhase n := by
  unfold rootPhase
  have heq : Complex.I*Real.pi*(((n+1024:ℕ):ℂ)/512) =
    Complex.I*Real.pi*((n:ℂ)/512)+(2*Real.pi*Complex.I) := by push_cast; ring
  rw [heq,Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]

lemma rootPhase_mod (n : ℕ) : rootPhase (n%1024) = rootPhase n := by
  have hp : Function.Periodic rootPhase 1024 := rootPhase_periodic
  exact hp.map_mod_nat n

lemma rootPhase_cos (n : ℕ) : (rootPhase n).re = Real.cos (Real.pi*((n:ℝ)/512)) := by
  unfold rootPhase
  rw [Complex.exp_re]
  simp only [Complex.mul_re,Complex.mul_im,Complex.div_ofNat_re,Complex.div_ofNat_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,Complex.natCast_re,
    Complex.natCast_im,zero_mul,mul_zero,sub_zero,zero_add,one_mul,
    zero_div,Real.exp_zero]


end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Fejer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fejér quadrature enclosures

Certified nodes and weights for the 256-node cosine quadrature rule.
-/

namespace SharpPlanar
open IntegerIntervals

lemma fejer_root_cos (v a : ℕ) :
    (rootPhase (2*a*(2*v+1))).re = Real.cos (2*(a:ℝ)*fejerAngle v) := by
  rw [rootPhase_cos]
  unfold fejerAngle
  congr 1
  push_cast
  ring

lemma fejerWeight_checked (v : ℕ) (a b : RBox) (ha : a.Contains (fejerPartial v 127))
    (he : ((RBox.rat 1 1).add (a.scale (-2) 1)).scale 1 256 = b) :
    b.Contains (fejerWeight v) := by
  rw [← he]
  have hh := RBox.contains_scale (RBox.contains_add (RBox.contains_rat 1 1 (by norm_num))
    (RBox.contains_scale ha (-2) 1 (by norm_num))) 1 256 (by norm_num)
  rw [fejer_partial_eq] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  unfold fejerWeight
  push_cast
  ring

lemma fejerNode_root (v : ℕ) : fejerNode v = (rootPhase (2*v+1)).re := by
  rw [rootPhase_cos]
  unfold fejerNode fejerAngle
  congr 1
  push_cast
  ring

end SharpPlanar

namespace SharpPlanar.IntegerCompact
open IntegerIntervals

def weight0 : RBox := ⟨32854899021958510264571372,32854899021958510264684290⟩
def weight1 : RBox := ⟨115643890836329592300920991,115643890836329592301652707⟩
def weight2 : RBox := ⟨186425341186478142130637142,186425341186478142132071158⟩
def weight3 : RBox := ⟨264792628993592540896364518,264792628993592540898468111⟩
def weight4 : RBox := ⟨337625197927180191466743821,337625197927180191469520764⟩
def weight5 : RBox := ⟨414695778421447914954232494,414695778421447914957689225⟩
def weight6 : RBox := ⟨488189937000491145122329595,488189937000491145126467967⟩
def weight7 : RBox := ⟨564585313122083449406883548,564585313122083449411708570⟩
def weight8 : RBox := ⟨638317675207538393581834267,638317675207538393587343582⟩
def weight9 : RBox := ⟨714227765284898142560721054,714227765284898142566835076⟩
def weight10 : RBox := ⟨787997020780326835710053428,787997020780326835716892278⟩
def weight11 : RBox := ⟨863485783121840440251192337,863485783121840440258718471⟩
def weight12 : RBox := ⟨937167764013815150899287971,937167764013815150907451278⟩
def weight13 : RBox := ⟨1012249534291717575608623519,1012249534291717575617377085⟩
def weight14 : RBox := ⟨1085753824000420340315222767,1085753824000420340324713544⟩
def weight15 : RBox := ⟨1160419579996777923424081859,1160419579996777923434294798⟩
def weight16 : RBox := ⟨1233672901838719242063693439,1233672901838719242074583778⟩
def weight17 : RBox := ⟨1307901266852325226207371856,1307901266852325226218877348⟩
def weight18 : RBox := ⟨1380840026805233674564253760,1380840026805233674576336188⟩
def weight19 : RBox := ⟨1454602544552288260551142916,1454602544552288260564135431⟩
def weight20 : RBox := ⟨1527169088187803451402758321,1527169088187803451416235366⟩
def weight21 : RBox := ⟨1600433014992203402676425795,1600433014992203402690394316⟩
def weight22 : RBox := ⟨1672573587728020047536379128,1672573587728020047551275851⟩
def weight23 : RBox := ⟨1745303488581413123273844206,1745303488581413123289152695⟩
def weight24 : RBox := ⟨1816967052637353898950070577,1816967052637353898966224051⟩
def weight25 : RBox := ⟨1889125772053601543611958466,1889125772053601543629036949⟩
def weight26 : RBox := ⟨1960263286585925611396448845,1960263286585925611413821417⟩
def weight27 : RBox := ⟨2031812570769548302370422369,2031812570769548302388653767⟩
def weight28 : RBox := ⟨2102376537417226956261905336,2102376537417226956280224648⟩
def weight29 : RBox := ⟨2173277451385880597969454359,2173277451385880597988851991⟩
def weight30 : RBox := ⟨2243221619351013954728161609,2243221619351013954748284485⟩
def weight31 : RBox := ⟨2313434838032280323185484641,2313434838032280323206471113⟩
def weight32 : RBox := ⟨2382714008961423530853016570,2382714008961423530873945017⟩
def weight33 : RBox := ⟨2452200027868549999065623669,2452200027868549999087532266⟩
def weight34 : RBox := ⟨2520769925313023080757748879,2520769925313023080780476129⟩
def weight35 : RBox := ⟨2589489218210731982105629167,2589489218210731982129273601⟩
def weight36 : RBox := ⟨2657306400097242267236794690,2657306400097242267261517376⟩
def weight37 : RBox := ⟨2725219540718512429700730282,2725219540718512429724967257⟩
def weight38 : RBox := ⟨2792241341182642226017712775,2792241341182642226042794226⟩
def weight39 : RBox := ⟨2859309099941888586034171026,2859309099941888586059884613⟩
def weight40 : RBox := ⟨2925493591637947329143346558,2925493591637947329169901907⟩
def weight41 : RBox := ⟨2991677014551349386351111171,2991677014551349386378554997⟩
def weight42 : RBox := ⟨3056982985503579824197139599,3056982985503579824225456620⟩
def weight43 : RBox := ⟨3122243460179323820935372368,3122243460179323820962774638⟩
def weight44 : RBox := ⟨3186630401119962167500951173,3186630401119962167529518099⟩
def weight45 : RBox := ⟨3250929713166444687604013502,3250929713166444687633456753⟩
def weight46 : RBox := ⟨3314357812533848584803790568,3314357812533848584834344507⟩
def weight47 : RBox := ⟨3377658194733971570150282385,3377658194733971570181313304⟩
def weight48 : RBox := ⟨3440088339323272551877889125,3440088339323272551909791348⟩
def weight49 : RBox := ⟨3502352515249085836173697390,3502352515249085836206540493⟩
def weight50 : RBox := ⟨3563746295065386521636763529,3563746295065386521670600773⟩
def weight51 : RBox := ⟨3624937518344627753212409149,3624937518344627753244187615⟩
def weight52 : RBox := ⟨3685257234595085284362657313,3685257234595085284395643772⟩
def weight53 : RBox := ⟨3745339324718025582912840989,3745339324718025582946757593⟩
def weight54 : RBox := ⟨3804548000151240159002014035,3804548000151240159036827563⟩
def weight55 : RBox := ⟨3863485375477059329230206922,3863485375477059329265775521⟩
def weight56 : RBox := ⟨3921546766472693407786744533,3921546766472693407823247213⟩
def weight57 : RBox := ⟨3979304474929752085786739772,3979304474929752085823420507⟩
def weight58 : RBox := ⟨4036183084882287367011186813,4036183084882287367048768249⟩
def weight59 : RBox := ⟨4092726832736535951842881697,4092726832736535951881047303⟩
def weight60 : RBox := ⟨4148387926380572560405783704,4148387926380572560444667908⟩
def weight61 : RBox := ⟨4203684105357756689347247211,4203684105357756689386809776⟩
def weight62 : RBox := ⟨4258093723759144794982340322,4258093723759144795022646015⟩
def weight63 : RBox := ⟨4312109436740432513532833577,4312109436740432513573832333⟩
def weight64 : RBox := ⟨4365234412735279897693917680,4365234412735279897730965810⟩
def weight65 : RBox := ⟨4417937498196211298645475243,4417937498196211298683967058⟩
def weight66 : RBox := ⟨4469745472103646047367985364,4469745472103646047407736227⟩
def weight67 : RBox := ⟨4521104527428516025268053090,4521104527428516025308869170⟩
def weight68 : RBox := ⟨4571563962896684265919348515,4571563962896684265961169848⟩
def weight69 : RBox := ⟨4621548366671504275910620453,4621548366671504275953595050⟩
def weight70 : RBox := ⟨4670628566542280100406672370,4670628566542280100450335668⟩
def weight71 : RBox := ⟨4719208499907091423913653871,4719208499907091423958310713⟩
def weight72 : RBox := ⟨4766879622005270934461156066,4766879622005270934506893110⟩
def weight73 : RBox := ⟨4814026089129177405541274014,4814026089129177405586692181⟩
def weight74 : RBox := ⟨4860259161897908846125205151,4860259161897908846171771874⟩
def weight75 : RBox := ⟨4905944009626571011820739023,4905944009626571011868183188⟩
def weight76 : RBox := ⟨4950710947543460949446198875,4950710947543460949494668528⟩
def weight77 : RBox := ⟨4994906884258064817896192089,4994906884258064817945143243⟩
def weight78 : RBox := ⟨5038180502976556968602523833,5038180502976556968652511470⟩
def weight79 : RBox := ⟨5080861116694780349872131194,5080861116694780349922812725⟩
def weight80 : RBox := ⟨5122615147863599496077058279,5122615147863599496128586170⟩
def weight81 : RBox := ⟨5163754923606351388193965764,5163754923606351388246311318⟩
def weight82 : RBox := ⟨5203964029326471386036971237,5203964029326471386090275722⟩
def weight83 : RBox := ⟨5243538365768798222281081767,5243538365768798222335283451⟩
def weight84 : RBox := ⟨5282178152652859128880119892,5282178152652859128935269874⟩
def weight85 : RBox := ⟨5320163378073107812640346059,5320163378073107812687155434⟩
def weight86 : RBox := ⟨5357210410876725006568461725,5357210410876725006616718030⟩
def weight87 : RBox := ⟨5393583798414604488183752538,5393583798414604488233198368⟩
def weight88 : RBox := ⟨5429015613212777300093035064,5429015613212777300143507747⟩
def weight89 : RBox := ⟨5463755395444195765818327306,5463755395444195765869783867⟩
def weight90 : RBox := ⟨5497550512329186233885497466,5497550512329186233937704682⟩
def weight91 : RBox := ⟨5530635895163525312794999161,5530635895163525312847895961⟩
def weight92 : RBox := ⟨5562773830443257907889391218,5562773830443257907943286989⟩
def weight93 : RBox := ⟨5594185006346973022951936561,5594185006346973023006345981⟩
def weight94 : RBox := ⟨5624646284225296969628806005,5624646284225296969684011897⟩
def weight95 : RBox := ⟨5654364444774320582459724612,5654364444774320582515799649⟩
def weight96 : RBox := ⟨5683130608496451681330841381,5683130608496451681386793267⟩
def weight97 : RBox := ⟨5711137956258757353545980461,5711137956258757353602979817⟩
def weight98 : RBox := ⟨5738191578706934836420499339,5738191578706934836477926701⟩
def weight99 : RBox := ⟨5764471338455741720009888145,5764471338455741720068327548⟩
def weight100 : RBox := ⟨5789796032181644714564789747,5789796032181644714623896598⟩
def weight101 : RBox := ⟨5814332461439061669678303244,5814332461439061669738242470⟩
def weight102 : RBox := ⟨5837912888120867156421880561,5837912888120867156479479947⟩
def weight103 : RBox := ⟨5860691287031258742944125056,5860691287031258743002818748⟩
def weight104 : RBox := ⟨5882513166344419020279517789,5882513166344419020338985693⟩
def weight105 : RBox := ⟨5903519886876394149683081285,5903519886876394149743135384⟩
def weight106 : RBox := ⟨5923570004768291589841432042,5923570004768291589902254387⟩
def weight107 : RBox := ⟨5942792459243946814942791692,5942792459243946815004006348⟩
def weight108 : RBox := ⟨5961058675603567321367733201,5961058675603567321429518010⟩
def weight109 : RBox := ⟨5978485344553441828649813117,5978485344553441828712371674⟩
def weight110 : RBox := ⟨5994956600268112465129793706,5994956600268112465191587026⟩
def weight111 : RBox := ⟨6010577039610215329321111218,6010577039610215329383501659⟩
def weight112 : RBox := ⟨6025243363002289724447107809,6025243363002289724509915577⟩
def weight113 : RBox := ⟨6039048210543529021123302047,6039048210543529021186703621⟩
def weight114 : RBox := ⟨6051900723180687647293955314,6051900723180687647357112135⟩
def weight115 : RBox := ⟨6063881704439054837188115369,6063881704439054837251687435⟩
def weight116 : RBox := ⟨6074912626312625515276774213,6074912626312625515340247587⟩
def weight117 : RBox := ⟨6085062559658558052385052499,6085062559658558052448978448⟩
def weight118 : RBox := ⟨6094265213724962908278863582,6094265213724962908342833342⟩
def weight119 : RBox := ⟨6102578014840415589665675058,6102578014840415589729688779⟩
def weight120 : RBox := ⟨6109946830921520823412964797,6109946830921520823477045083⟩
def weight121 : RBox := ⟨6116417516575415400105359979,6116417516575415400169578642⟩
def weight122 : RBox := ⟨6121948034614205269491689602,6121948034614205269555839779⟩
def weight123 : RBox := ⟨6126572725753092566573313075,6126572725753092566637440834⟩
def weight124 : RBox := ⟨6130261598421713790436417950,6130261598421713790500332217⟩
def weight125 : RBox := ⟨6133037522574668035260086108,6133037522574668035323722931⟩
def weight126 : RBox := ⟨6134882517232499617024723204,6134882517232499617087919323⟩
def weight127 : RBox := ⟨6135808010229466395145471605,6135808010229466395208006666⟩
def weight128 : RBox := weight127
def weight129 : RBox := weight126
def weight130 : RBox := weight125
def weight131 : RBox := weight124
def weight132 : RBox := weight123
def weight133 : RBox := weight122
def weight134 : RBox := weight121
def weight135 : RBox := weight120
def weight136 : RBox := weight119
def weight137 : RBox := weight118
def weight138 : RBox := weight117
def weight139 : RBox := weight116
def weight140 : RBox := weight115
def weight141 : RBox := weight114
def weight142 : RBox := weight113
def weight143 : RBox := weight112
def weight144 : RBox := weight111
def weight145 : RBox := weight110
def weight146 : RBox := weight109
def weight147 : RBox := weight108
def weight148 : RBox := weight107
def weight149 : RBox := weight106
def weight150 : RBox := weight105
def weight151 : RBox := weight104
def weight152 : RBox := weight103
def weight153 : RBox := weight102
def weight154 : RBox := weight101
def weight155 : RBox := weight100
def weight156 : RBox := weight99
def weight157 : RBox := weight98
def weight158 : RBox := weight97
def weight159 : RBox := weight96
def weight160 : RBox := weight95
def weight161 : RBox := weight94
def weight162 : RBox := weight93
def weight163 : RBox := weight92
def weight164 : RBox := weight91
def weight165 : RBox := weight90
def weight166 : RBox := weight89
def weight167 : RBox := weight88
def weight168 : RBox := weight87
def weight169 : RBox := weight86
def weight170 : RBox := weight85
def weight171 : RBox := weight84
def weight172 : RBox := weight83
def weight173 : RBox := weight82
def weight174 : RBox := weight81
def weight175 : RBox := weight80
def weight176 : RBox := weight79
def weight177 : RBox := weight78
def weight178 : RBox := weight77
def weight179 : RBox := weight76
def weight180 : RBox := weight75
def weight181 : RBox := weight74
def weight182 : RBox := weight73
def weight183 : RBox := weight72
def weight184 : RBox := weight71
def weight185 : RBox := weight70
def weight186 : RBox := weight69
def weight187 : RBox := weight68
def weight188 : RBox := weight67
def weight189 : RBox := weight66
def weight190 : RBox := weight65
def weight191 : RBox := weight64
def weight192 : RBox := weight63
def weight193 : RBox := weight62
def weight194 : RBox := weight61
def weight195 : RBox := weight60
def weight196 : RBox := weight59
def weight197 : RBox := weight58
def weight198 : RBox := weight57
def weight199 : RBox := weight56
def weight200 : RBox := weight55
def weight201 : RBox := weight54
def weight202 : RBox := weight53
def weight203 : RBox := weight52
def weight204 : RBox := weight51
def weight205 : RBox := weight50
def weight206 : RBox := weight49
def weight207 : RBox := weight48
def weight208 : RBox := weight47
def weight209 : RBox := weight46
def weight210 : RBox := weight45
def weight211 : RBox := weight44
def weight212 : RBox := weight43
def weight213 : RBox := weight42
def weight214 : RBox := weight41
def weight215 : RBox := weight40
def weight216 : RBox := weight39
def weight217 : RBox := weight38
def weight218 : RBox := weight37
def weight219 : RBox := weight36
def weight220 : RBox := weight35
def weight221 : RBox := weight34
def weight222 : RBox := weight33
def weight223 : RBox := weight32
def weight224 : RBox := weight31
def weight225 : RBox := weight30
def weight226 : RBox := weight29
def weight227 : RBox := weight28
def weight228 : RBox := weight27
def weight229 : RBox := weight26
def weight230 : RBox := weight25
def weight231 : RBox := weight24
def weight232 : RBox := weight23
def weight233 : RBox := weight22
def weight234 : RBox := weight21
def weight235 : RBox := weight20
def weight236 : RBox := weight19
def weight237 : RBox := weight18
def weight238 : RBox := weight17
def weight239 : RBox := weight16
def weight240 : RBox := weight15
def weight241 : RBox := weight14
def weight242 : RBox := weight13
def weight243 : RBox := weight12
def weight244 : RBox := weight11
def weight245 : RBox := weight10
def weight246 : RBox := weight9
def weight247 : RBox := weight8
def weight248 : RBox := weight7
def weight249 : RBox := weight6
def weight250 : RBox := weight5
def weight251 : RBox := weight4
def weight252 : RBox := weight3
def weight253 : RBox := weight2
def weight254 : RBox := weight1
def weight255 : RBox := weight0
def weights0 : Fin 16 → RBox := ![weight0,weight1,weight2,weight3,weight4,weight5,weight6,weight7,weight8,weight9,weight10,weight11,weight12,weight13,weight14,weight15]
def weights1 : Fin 16 → RBox := ![weight16,weight17,weight18,weight19,weight20,weight21,weight22,weight23,weight24,weight25,weight26,weight27,weight28,weight29,weight30,weight31]
def weights2 : Fin 16 → RBox := ![weight32,weight33,weight34,weight35,weight36,weight37,weight38,weight39,weight40,weight41,weight42,weight43,weight44,weight45,weight46,weight47]
def weights3 : Fin 16 → RBox := ![weight48,weight49,weight50,weight51,weight52,weight53,weight54,weight55,weight56,weight57,weight58,weight59,weight60,weight61,weight62,weight63]
def weights4 : Fin 16 → RBox := ![weight64,weight65,weight66,weight67,weight68,weight69,weight70,weight71,weight72,weight73,weight74,weight75,weight76,weight77,weight78,weight79]
def weights5 : Fin 16 → RBox := ![weight80,weight81,weight82,weight83,weight84,weight85,weight86,weight87,weight88,weight89,weight90,weight91,weight92,weight93,weight94,weight95]
def weights6 : Fin 16 → RBox := ![weight96,weight97,weight98,weight99,weight100,weight101,weight102,weight103,weight104,weight105,weight106,weight107,weight108,weight109,weight110,weight111]
def weights7 : Fin 16 → RBox := ![weight112,weight113,weight114,weight115,weight116,weight117,weight118,weight119,weight120,weight121,weight122,weight123,weight124,weight125,weight126,weight127]
def weights8 : Fin 16 → RBox := ![weight128,weight129,weight130,weight131,weight132,weight133,weight134,weight135,weight136,weight137,weight138,weight139,weight140,weight141,weight142,weight143]
def weights9 : Fin 16 → RBox := ![weight144,weight145,weight146,weight147,weight148,weight149,weight150,weight151,weight152,weight153,weight154,weight155,weight156,weight157,weight158,weight159]
def weights10 : Fin 16 → RBox := ![weight160,weight161,weight162,weight163,weight164,weight165,weight166,weight167,weight168,weight169,weight170,weight171,weight172,weight173,weight174,weight175]
def weights11 : Fin 16 → RBox := ![weight176,weight177,weight178,weight179,weight180,weight181,weight182,weight183,weight184,weight185,weight186,weight187,weight188,weight189,weight190,weight191]
def weights12 : Fin 16 → RBox := ![weight192,weight193,weight194,weight195,weight196,weight197,weight198,weight199,weight200,weight201,weight202,weight203,weight204,weight205,weight206,weight207]
def weights13 : Fin 16 → RBox := ![weight208,weight209,weight210,weight211,weight212,weight213,weight214,weight215,weight216,weight217,weight218,weight219,weight220,weight221,weight222,weight223]
def weights14 : Fin 16 → RBox := ![weight224,weight225,weight226,weight227,weight228,weight229,weight230,weight231,weight232,weight233,weight234,weight235,weight236,weight237,weight238,weight239]
def weights15 : Fin 16 → RBox := ![weight240,weight241,weight242,weight243,weight244,weight245,weight246,weight247,weight248,weight249,weight250,weight251,weight252,weight253,weight254,weight255]
def weightRows : Fin 16 → Fin 16 → RBox := ![weights0,weights1,weights2,weights3,weights4,weights5,weights6,weights7,weights8,weights9,weights10,weights11,weights12,weights13,weights14,weights15]
end SharpPlanar.IntegerCompact


end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Quadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev



open MeasureTheory Set
open scoped BigOperators

namespace SharpPlanar
open MeasureTheory Set

lemma complexZ_differentiableAt {t : ℂ} (ht : t+Complex.I*(h:ℂ) ≠ 0) :
    DifferentiableAt ℂ complexZ t := by
  unfold complexZ
  fun_prop (disch := exact ht)
lemma complexTransformedFactor_differentiableAt {t : ℂ}
    (ht : t+Complex.I*(h:ℂ) ≠ 0) (m y : ℝ) (ell : ℕ) :
    DifferentiableAt ℂ (complexTransformedFactor m y ell) t := by
  have hL := complexLambda_differentiableAt ht
  have hZ := complexZ_differentiableAt ht
  unfold complexTransformedFactor
  fun_prop

lemma transformedIntegrand_analytic (c d : ℕ → ℝ) {j : ℕ} (hj : j < 6) (m y : ℝ) (ell : ℕ) :
    DiffContOnCl ℂ (fun w => finiteDensity c d j (diskAffine j w) *
      complexTransformedFactor m y ell (diskAffine j w)) (Metric.ball 0 2) := by
  apply DifferentiableOn.diffContOnCl
  intro w hw
  have hw' : ‖w‖ ≤ 2 := by
    rw [closure_ball (0:ℂ) (by norm_num : (2:ℝ) ≠ 0),Metric.mem_closedBall,dist_zero_right] at hw
    exact hw
  have ht := disk_denominator_ne hj (diskAffine_mem hw')
  have hA : DifferentiableAt ℂ (diskAffine j) w := by unfold diskAffine; fun_prop
  exact (((finiteDensity_differentiable c d j).differentiableAt.comp w hA).mul
    ((complexTransformedFactor_differentiableAt ht m y ell).comp w hA)).differentiableWithinAt

lemma transformedMoment_piece_average_error (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {j : ℕ} (hj : j < 6) {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100)
    (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖(1/2:ℂ)*(∫ x in (-1:ℝ)..1, finiteDensity c d j (diskAffine j x) *
        complexTransformedFactor m y ell (diskAffine j x)) -
      ∑ v : Fin 256, (fejerWeight v.val:ℂ)*
        (finiteDensity c d j (diskAffine j (fejerNode v.val)) *
          complexTransformedFactor m y ell (diskAffine j (fejerNode v.val)))‖ < 1/10^22 := by
  apply fejer_analytic_average_error _ (transformedIntegrand_analytic c d hj m y ell)
  intro w hw'
  apply transformedIntegrand_disk_bound c d hw hj (diskAffine_mem ?_) hm0 hm1 hy ell
  simpa only [Metric.mem_sphere,dist_zero_right] using le_of_eq hw'

end SharpPlanar

namespace SharpPlanar
open MeasureTheory

lemma transformedMoment_piece_error (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {j : ℕ} (hj : j < 6) {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100)
    (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖pieceIntegral (fun t => finiteDensity c d j t*complexTransformedFactor m y ell t) j-
      pieceRule (fun t => finiteDensity c d j t*complexTransformedFactor m y ell t) j‖ <
        (1/10^22)/6 :=
  piece_rule_error_scaling _ _ (transformedMoment_piece_average_error c d hw hj hm0 hm1 hy ell)

lemma transformedMoment_rule_error (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖(∑ j : Fin 6, pieceIntegral
        (fun t => finiteDensity c d j t*complexTransformedFactor m y ell t) j)-
      ∑ j : Fin 6, pieceRule
        (fun t => finiteDensity c d j t*complexTransformedFactor m y ell t) j‖ < 1/10^22 :=
  six_piece_error (fun j => transformedMoment_piece_error c d hw j.isLt hm0 hm1 hy ell)

end SharpPlanar

namespace SharpPlanar
open MeasureTheory

noncomputable def complexBasisMoment (d e : Bool) (n j m : ℕ) (t : ℂ) : ℂ :=
  complexBasis d n j t * complexTransformedFactor m 1 (if e then 1 else 0) t

lemma complexBasis_rule_error {n m : ℕ} (hn : n ≤ 100) (hm : m ≤ 100) (d e : Bool) :
    ‖(∑ j : Fin 6, pieceIntegral (complexBasisMoment d e n j.val m) j.val)-
      ∑ j : Fin 6, pieceRule (complexBasisMoment d e n j.val m) j.val‖ < 1/10^22 := by
  have hw1 : ∑ k ∈ Finset.range 101, (|singleCoefficient n k|+|(0:ℝ)|) ≤ 3 := by
    simp only [abs_zero,add_zero,singleCoefficient_mass hn]; norm_num
  have hw2 : ∑ k ∈ Finset.range 101, (|(0:ℝ)|+|singleCoefficient n k|) ≤ 3 := by
    simp only [abs_zero,zero_add,singleCoefficient_mass hn]; norm_num
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hm1 : (m:ℝ) ≤ 100 := by exact_mod_cast hm
  unfold complexBasisMoment complexBasis
  cases d
  · simpa only [singleDensity_u hn,Bool.false_eq_true,ite_false, if_false]
      using transformedMoment_rule_error (singleCoefficient n) (fun _ => 0) hw1
        hm0 hm1 (y := 1) (by norm_num) (if e then 1 else 0)
  · simpa only [singleDensity_v hn,ite_true, if_true]
      using transformedMoment_rule_error (fun _ => 0) (singleCoefficient n) hw2
        hm0 hm1 (y := 1) (by norm_num) (if e then 1 else 0)

end SharpPlanar


end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma pointZ_eq (t : ℝ) : pointZ t = z t := by
  unfold pointZ z B h
  push_cast
  rfl

noncomputable def basisMoment (d e : Bool) (n j m : ℕ) (t : ℝ) : ℂ :=
  basisFunction d n j t * (lambda t*Complex.exp (Complex.I*Real.pi*z t*m)) *
    (if e then Complex.I*Real.pi*z t else 1)

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

noncomputable def momentRuleValue (t : ℕ → ℕ → ℝ) (w : ℕ → ℝ)
    (n m : ℕ) (d e : Bool) : ℂ :=
  ∑ j : Fin 6, (1/6:ℂ)*∑ v : Fin 256, (w v.val:ℂ)*
    basisMoment d e n j.val m (t j.val v.val)

end SharpPlanar.IntegerBasis

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerCompact

lemma complexZ_ofReal (t : ℝ) : complexZ t = z t := rfl
lemma complexBasisMoment_ofReal (d e : Bool) (n j m : ℕ) (t : ℝ) :
    complexBasisMoment d e n j m t = basisMoment d e n j m t := by
  unfold complexBasisMoment complexBasis basisMoment basisFunction complexTransformedFactor
  rw [complexU_ofReal,complexV_ofReal,complexLambda_ofReal,complexZ_ofReal]
  cases d <;> cases e <;> simp <;> ring


end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quadrature enclosures for cardinal moments

The certified quadrature grid and cardinal basis enclosures bound the finite moment rule.
-/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid IntegerCompact

lemma basis_rule_value (n m : ℕ) (d e : Bool) :
    (∑ j : Fin 6, pieceRule (complexBasisMoment d e n j.val m) j.val) =
      momentRuleValue quadraturePoint fejerWeight n m d e := by
  unfold pieceRule momentRuleValue
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  have ht : diskAffine j.val (fejerNode v.val) = (quadraturePoint j.val v.val:ℂ) := by
    unfold diskAffine diskCenter quadraturePoint
    push_cast
    ring
  rw [ht,complexBasisMoment_ofReal]

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Entries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Entries of the cardinal interpolation operator

The columns of the interpolation operator are cardinal basis functions, and
certified quadrature controls their value and derivative entries.
-/

namespace SharpPlanar
open IntegerBasis IntegerIntervals IntegerGrid


lemma K_column_integral (n : Node) (d e : Bool) (m : ℕ) :
    K (positiveData (columnVector n d)) (if e then 1 else 0) m =
      (∑ j : Fin 6, pieceIntegral (complexBasisMoment d e n.val j.val m) j.val).re := by
  unfold K positiveData
  simp only [Complex.ofReal_zero,zero_mul,zero_add]
  rw [← Finset.sum_range (fun j => pieceIntegral (complexBasisMoment d e n.val j m) j)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  unfold pieceIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [complexBasisMoment_ofReal,show density { C := 0, c₀ := 0, d₀ := 0, x := columnVector n d } j t = basisFunction d n.val j t from density_column n d j t]
  unfold kernelMoment basisMoment
  (cases e <;> simp); ring


lemma K_column_rule_error {n : Node} {m : ℕ} (hn : n.val ≤ 100) (hm : m ≤ 100)
    (d e : Bool) :
    |K (positiveData (columnVector n d)) (if e then 1 else 0) m -
      (momentRuleValue quadraturePoint fejerWeight n.val m d e).re| < 1/10^22 := by
  rw [K_column_integral,← basis_rule_value]
  exact (Complex.abs_re_le_norm _).trans_lt (complexBasis_rule_error hn hm d e)

lemma S_column_value (n m : Node) (d : Bool) :
    S (columnVector n d) (m,false) = -K (positiveData (columnVector n d)) 0 m.val / Q m.val := by
  simp [S_apply,Scoords]

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_NodeIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
namespace Numerical

def qSmall : RBox := ((piBounds.mul piBounds).scale 2 3).mul
  ((RBox.rat 2 1).add (bBounds.scale (-2) 1))
def qLarge : RBox := ((piBounds.mul piBounds).scale 2 3).mul
  ((RBox.rat 2 1).add (bBounds.scale 2 1))
def qBase : RBox := (piBounds.mul piBounds).scale 1 3

def dSmall : RBox := (piBounds.mul ((RBox.rat 3 1).add (bBounds.scale 2 1))).scale 1 18
def dOther : RBox := (piBounds.mul ((RBox.rat 3 1).add (bBounds.scale (-2) 1))).scale 1 18
def dBase : RBox := (piBounds.mul bBounds).scale 7 9

lemma qSmall_contains : qSmall.Contains ((2*Real.pi^2/3)*(2-2*b)) := by
  have hp := RBox.contains_scale (RBox.contains_mul piBounds_contains piBounds_contains) 2 3 (by norm_num)
  have hb := RBox.contains_add (RBox.contains_rat 2 1 (by norm_num))
    (RBox.contains_scale bBounds_contains (-2) 1 (by norm_num))
  convert RBox.contains_mul hp hb using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring)
lemma qLarge_contains : qLarge.Contains ((2*Real.pi^2/3)*(2+2*b)) := by
  have hp := RBox.contains_scale (RBox.contains_mul piBounds_contains piBounds_contains) 2 3 (by norm_num)
  have hb := RBox.contains_add (RBox.contains_rat 2 1 (by norm_num))
    (RBox.contains_scale bBounds_contains 2 1 (by norm_num))
  convert RBox.contains_mul hp hb using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> (ring_nf; simp))
lemma qBase_contains : qBase.Contains (Real.pi^2/3) := by
  convert RBox.contains_scale (RBox.contains_mul piBounds_contains piBounds_contains) 1 3 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qBase] <;> ring)
lemma dSmall_contains : dSmall.Contains (Real.pi*(3+2*b)/18) := by
  have hb := RBox.contains_add (RBox.contains_rat 3 1 (by norm_num))
    (RBox.contains_scale bBounds_contains 2 1 (by norm_num))
  convert RBox.contains_scale (RBox.contains_mul piBounds_contains hb) 1 18 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring)
lemma dOther_contains : dOther.Contains (Real.pi*(3-2*b)/18) := by
  have hb := RBox.contains_add (RBox.contains_rat 3 1 (by norm_num))
    (RBox.contains_scale bBounds_contains (-2) 1 (by norm_num))
  convert RBox.contains_scale (RBox.contains_mul piBounds_contains hb) 1 18 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring)
lemma dBase_contains : dBase.Contains (7*Real.pi*b/9) := by
  convert RBox.contains_scale (RBox.contains_mul piBounds_contains bBounds_contains) 7 9 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring)

def qBox (n : ℕ) : RBox := if n%12=0 ∨ n%12=4 then qBase else if n%12=1 ∨ n%12=3 then qSmall else qLarge
def dBox (n : ℕ) : RBox := match n%12 with
  | 0 => dBase.neg
  | 1 => dSmall
  | 3 => dSmall.neg
  | 4 => dBase
  | 7 => dOther.neg
  | _ => dOther

lemma qBox_contains (n : ℕ) (hn : n%12 ∈ residues) : (qBox n).Contains (Q n) := by
  have hh : Q n = Q (n%12) := by simp [Q]
  rw [hh]
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with hn|hn|hn|hn|hn|hn <;> simp only [hn, qBox] <;>
    norm_num only at *
  · simpa [Q_0,hn,qBox] using qBase_contains
  · simpa [Q_1,hn,qBox] using qSmall_contains
  · simpa [Q_3,hn,qBox] using qSmall_contains
  · simpa [Q_4,hn,qBox] using qBase_contains
  · simpa [Q_7,hn,qBox] using qLarge_contains
  · simpa [Q_9,hn,qBox] using qLarge_contains
lemma dBox_contains (n : ℕ) (hn : n%12 ∈ residues) : (dBox n).Contains (D n) := by
  have hh : D n = D (n%12) := by simp [D]
  rw [hh]
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with hn|hn|hn|hn|hn|hn
  · simpa [D_0,hn,dBox,neg_mul,neg_div] using RBox.neg_contains dBase_contains
  · simpa [D_1,hn,dBox] using dSmall_contains
  · simpa [D_3,hn,dBox,neg_mul,neg_div] using RBox.neg_contains dSmall_contains
  · simpa [D_4,hn,dBox] using dBase_contains
  · simpa [D_7,hn,dBox,neg_mul,neg_div] using RBox.neg_contains dOther_contains
  · simpa [D_9,hn,dBox] using dOther_contains

def invBox (a : RBox) : RBox := ⟨precision^2/a.hi,-((-precision^2)/a.lo)⟩
def qiBox (n : ℕ) : RBox := invBox (qBox n)
lemma qiBox_contains (n : ℕ) (hn : n%12 ∈ residues) : (qiBox n).Contains (Q n)⁻¹ := by
  apply RBox.inv_contains (qBox_contains n hn)
  unfold qiBox qBox
  split <;> (try split) <;> decide +kernel

def inflate (a : RBox) : RBox := ⟨a.lo-10^8,a.hi+10^8⟩
lemma inflate_contains {a : RBox} {x y : ℝ} (hx : a.Contains x) (he : |y-x| < 1/10^22) :
    (inflate a).Contains y := by
  have he' := abs_lt.mp he
  have hp := precision_pos
  have hL := mul_lt_mul_of_pos_left he'.1 hp
  have hU := mul_lt_mul_of_pos_left he'.2 hp
  constructor <;> dsimp [inflate] <;> push_cast <;>
    norm_num [RBox.Contains,precision] at hL hU hx ⊢ <;> linarith only [hx.1,hx.2,hL,hU]

lemma S_column_value_contains {n m : Node} {d : Bool} {a : RBox}
    (ha : a.Contains (K (positiveData (columnVector n d)) 0 m.val)) :
    (a.neg.mul (qiBox m.val)).Contains (S (columnVector n d) (m,false)) := by
  rw [S_column_value,div_eq_mul_inv]
  exact RBox.contains_mul (RBox.neg_contains ha) (qiBox_contains m.val m.property.2)
end Numerical
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_DEntries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def Dmat : Matrix (Fin 6) (Fin 6) ℝ := fun i j => S (columnVector (jNode j) (jDeriv j)) (jNode i,jDeriv i)
noncomputable def dentry0_0 : RBox := ⟨(-245926663229645305249767762805),(-245926663229645304859284756738)⟩
noncomputable def dentry3_0 : RBox := ⟨424700589287547025857931921651,424700589287547027999275868645⟩
noncomputable def dentry0_3 : RBox := ⟨30452555066926640622749259400,30452555066926640828004301927⟩
noncomputable def dentry3_3 : RBox := ⟨931968827424315928087138852293,931968827424315929373850684394⟩
noncomputable def dentry1_0 : RBox := ⟨(-23655100336718873202242240942),(-23655100336718873120273669237)⟩
noncomputable def dentry4_0 : RBox := ⟨145671047970350036773325436387,145671047970350037199231909594⟩
noncomputable def dentry1_3 : RBox := ⟨80528838586735272363974753180,80528838586735272472281451816⟩
noncomputable def dentry4_3 : RBox := ⟨521756342810954494199096553637,521756342810954494790549200675⟩
noncomputable def dentry2_0 : RBox := ⟨(-1097737034296297013723665259),(-1097737034296296987012474958)⟩
noncomputable def dentry5_0 : RBox := ⟨(-49222269312866616533668297810),(-49222269312866616362895656546)⟩
noncomputable def dentry2_3 : RBox := ⟨(-56406703537031364478831607653),(-56406703537031364430188588560)⟩
noncomputable def dentry5_3 : RBox := ⟨27834593699646376815605650731,27834593699646377127655114131⟩
noncomputable def dentry0_1 : RBox := ⟨84919083920626310662179677360,84919083920626310963649378583⟩
noncomputable def dentry3_1 : RBox := ⟨(-401818617642335374122553965636),(-401818617642335372392607050014)⟩
noncomputable def dentry0_4 : RBox := ⟨(-106450383559834775553375548749),(-106450383559834775291307669099)⟩
noncomputable def dentry3_4 : RBox := ⟨51160635846592449630662157438,51160635846592451095925214287⟩
noncomputable def dentry1_1 : RBox := ⟨(-58681970988985215880538687120),(-58681970988985215799134371859)⟩
noncomputable def dentry4_1 : RBox := ⟨(-13628559633735631908901705881),(-13628559633735631522414018748)⟩
noncomputable def dentry1_4 : RBox := ⟨(-9335195132489238242468768282),(-9335195132489238117842659765)⟩
noncomputable def dentry4_4 : RBox := ⟨696603759878277757337123237275,696603759878277758050967540167⟩
noncomputable def dentry2_1 : RBox := ⟨11552892703545774298548951595,11552892703545774325348299103⟩
noncomputable def dentry5_1 : RBox := ⟨(-85515720483106714613961869326),(-85515720483106714442684097804)⟩
noncomputable def dentry2_4 : RBox := ⟨(-46599334773430376018515334202),(-46599334773430375961386819313)⟩
noncomputable def dentry5_4 : RBox := ⟨(-113965371204432533744771266896),(-113965371204432533377810928653)⟩
noncomputable def dentry0_2 : RBox := ⟨38513567412242708706244438853,38513567412242709174634148764⟩
noncomputable def dentry3_2 : RBox := ⟨227145133131591005392854971615,227145133131591008209757733306⟩
noncomputable def dentry0_5 : RBox := ⟨(-35236824314615944648195425884),(-35236824314615944265946143652)⟩
noncomputable def dentry3_5 : RBox := ⟨13947539579869521084614770631,13947539579869523328647289424⟩
noncomputable def dentry1_2 : RBox := ⟨(-50367220418701310824260347488),(-50367220418701310746671987499)⟩
noncomputable def dentry4_2 : RBox := ⟨(-140501438496878817810768594789),(-140501438496878817401660852855)⟩
noncomputable def dentry1_5 : RBox := ⟨(-65563767968601851989120599895),(-65563767968601851839857744056)⟩
noncomputable def dentry4_5 : RBox := ⟨617641971506705838665457646400,617641971506705839485675654971⟩
noncomputable def dentry2_2 : RBox := ⟨16906689819273463213216826620,16906689819273463235453873264⟩
noncomputable def dentry5_2 : RBox := ⟨(-78390776109438054485518877398),(-78390776109438054339396429593)⟩
noncomputable def dentry2_5 : RBox := ⟨(-32138315292585356201983505971),(-32138315292585356140057198794)⟩
noncomputable def dentry5_5 : RBox := ⟨(-197772066238261852433723686168),(-197772066238261852031962127069)⟩
noncomputable def dEntries : Matrix (Fin 6) (Fin 6) RBox := ![![dentry0_0,dentry0_1,dentry0_2,dentry0_3,dentry0_4,dentry0_5],
![dentry1_0,dentry1_1,dentry1_2,dentry1_3,dentry1_4,dentry1_5],
![dentry2_0,dentry2_1,dentry2_2,dentry2_3,dentry2_4,dentry2_5],
![dentry3_0,dentry3_1,dentry3_2,dentry3_3,dentry3_4,dentry3_5],
![dentry4_0,dentry4_1,dentry4_2,dentry4_3,dentry4_4,dentry4_5],
![dentry5_0,dentry5_1,dentry5_2,dentry5_3,dentry5_4,dentry5_5]]
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerIntervals
open scoped BigOperators

def sumBox {ι : Type*} [Fintype ι] (a : ι → RBox) : RBox :=
  ⟨∑ i, (a i).lo, ∑ i, (a i).hi⟩
lemma sumBox_contains {ι : Type*} [Fintype ι] {a : ι → RBox} {x : ι → ℝ}
    (ha : ∀ i, (a i).Contains (x i)) : (sumBox a).Contains (∑ i, x i) := by
  constructor
  · simpa only [sumBox,Int.cast_sum,Finset.mul_sum] using Finset.sum_le_sum (fun i _ => (ha i).1)
  · simpa only [sumBox,Int.cast_sum,Finset.mul_sum] using Finset.sum_le_sum (fun i _ => (ha i).2)

def matrixMulBox {n m k : ℕ} (a : Matrix (Fin n) (Fin m) RBox)
    (b : Matrix (Fin m) (Fin k) RBox) : Matrix (Fin n) (Fin k) RBox :=
  fun i j => sumBox (fun l => (a i l).mul (b l j))
lemma matrixMulBox_contains {n m k : ℕ} {a : Matrix (Fin n) (Fin m) RBox}
    {b : Matrix (Fin m) (Fin k) RBox} {A : Matrix (Fin n) (Fin m) ℝ}
    {B : Matrix (Fin m) (Fin k) ℝ} (ha : ∀ i j, (a i j).Contains (A i j))
    (hb : ∀ i j, (b i j).Contains (B i j)) (i j) :
    (matrixMulBox a b i j).Contains ((A*B) i j) := by
  exact sumBox_contains (fun l => RBox.contains_mul (ha i l) (hb l j))

lemma column_bound_lt {n m : ℕ} {a : Matrix (Fin n) (Fin m) RBox}
    {A : Matrix (Fin n) (Fin m) ℝ} {u v : ℤ} (hv : 0 < v)
    (ha : ∀ i j, (a i j).Contains (A i j))
    (hc : ∀ j, (∑ i, (a i j).bound)*v < precision*u) :
    ∀ j, ∑ i, |A i j| < (u:ℝ)/v := by
  intro j
  have h₁ : (precision:ℝ)*(∑ i, |A i j|) ≤ (∑ i, ((a i j).bound:ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => RBox.abs_bound (ha i j)
  have hv' : (0:ℝ) < v := by exact_mod_cast hv
  have h₂ : (∑ i, ((a i j).bound:ℝ))*(v:ℝ) < (precision:ℝ)*u := by
    exact_mod_cast hc j
  apply (mul_lt_mul_iff_right₀ precision_pos).mp
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ hv').mpr
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right h₁ hv'.le) h₂

end SharpPlanar.IntegerIntervals

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LEntries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def lentry0_0 : RBox := ⟨386164739228853845759773052,386164739228853847338729471⟩
noncomputable def lentry1_0 : RBox := ⟨49064967585188068869174563,49064967585188069987341210⟩
noncomputable def lentry2_0 : RBox := ⟨349955633020704232195660108,349955633020704238293079170⟩
noncomputable def lentry10_0 : RBox := ⟨735342424357373673845647416,735342424357373720939652077⟩
noncomputable def lentry11_0 : RBox := ⟨(-373604188084837902044523338),(-373604188084837871188935056)⟩
noncomputable def lentry0_3 : RBox := ⟨1237841529233122015925964342,1237841529233122021272149662⟩
noncomputable def lentry1_3 : RBox := ⟨(-945531822378341432500259730),(-945531822378341427352180742)⟩
noncomputable def lentry10_3 : RBox := ⟨15723242855704063078702190943,15723242855704063465727922119⟩
noncomputable def lentry11_3 : RBox := ⟨(-1539994406308444939497564809),(-1539994406308444667344235719)⟩
noncomputable def lentry0_1 : RBox := ⟨486118439120750072856567422,486118439120750074559192952⟩
noncomputable def lentry1_1 : RBox := ⟨119087850140090609779608152,119087850140090611010500019⟩
noncomputable def lentry2_1 : RBox := ⟨358967247032856833332163871,358967247032856840141352766⟩
noncomputable def lentry10_1 : RBox := ⟨710843065811023928625760408,710843065811023981701947655⟩
noncomputable def lentry11_1 : RBox := ⟨(-467966495451986099247977206),(-467966495451986064390183177)⟩
noncomputable def lentry0_4 : RBox := ⟨2125600111687210926303952134,2125600111687210932405875170⟩
noncomputable def lentry1_4 : RBox := ⟨(-780891265784406832000933468),(-780891265784406826200208949)⟩
noncomputable def lentry10_4 : RBox := ⟨17181475429765936689474771825,17181475429765937119960748674⟩
noncomputable def lentry11_4 : RBox := ⟨(-2380512632259958830256652294),(-2380512632259958528106206527)⟩
noncomputable def lentry0_2 : RBox := ⟨485328626881395931714985849,485328626881395932971229801⟩
noncomputable def lentry1_2 : RBox := ⟨159432915114858452138511907,159432915114858453113123532⟩
noncomputable def lentry10_2 : RBox := ⟨667100822413377830267050569,667100822413377880297221997⟩
noncomputable def lentry11_2 : RBox := ⟨(-515958726858467410477971212),(-515958726858467377164471438)⟩
noncomputable def lentry0_5 : RBox := ⟨2615176994895548135832210442,2615176994895548142063566693⟩
noncomputable def lentry1_5 : RBox := ⟨(-641704209447256286883620943),(-641704209447256281007240349)⟩
noncomputable def lentry10_5 : RBox := ⟨17872500092793652677529018879,17872500092793653116898410653⟩
noncomputable def lentry11_5 : RBox := ⟨(-2872552850724879556441069579),(-2872552850724879247571465752)⟩
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_1_0
noncomputable def realAnswer : RBox := ⟨44079102290252843909020610113,44079102290277870526000247299⟩
end tm0_1_0

namespace tm0_1_1
noncomputable def realAnswer : RBox := ⟨(-687802679169301412656633638910),(-687802679169174356239334719831)⟩
end tm0_1_1

namespace tm1_1_0
noncomputable def realAnswer : RBox := ⟨118244842056019900934652075450,118244842056040446386396701403⟩
end tm1_1_0

namespace tm1_1_1
noncomputable def realAnswer : RBox := ⟨(-537276096718696872011556700675),(-537276096718592567153537579701)⟩
end tm1_1_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_100_0
noncomputable def realAnswer : RBox := ⟨30747440053207996527,30747465985898952035⟩
end tm0_100_0

namespace tm0_100_1
noncomputable def realAnswer : RBox := ⟨734176249133530551840,734176348487575808725⟩
end tm0_100_1

namespace tm1_100_0
noncomputable def realAnswer : RBox := ⟨(-50868015716281031316),(-50868014768622190753)⟩
end tm1_100_0

namespace tm1_100_1
noncomputable def realAnswer : RBox := ⟨(-892173633171178659828),(-892173629534357930919)⟩
end tm1_100_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_12_0
noncomputable def realAnswer : RBox := ⟨1975691615871230834443090122,1975691615871231772272876838⟩
end tm0_12_0

namespace tm0_12_1
noncomputable def realAnswer : RBox := ⟨(-15487721246398204038326400981),(-15487721246398200041669254304)⟩
end tm0_12_1

namespace tm1_12_0
noncomputable def realAnswer : RBox := ⟨(-1199799242832934988821215397),(-1199799242832934231651485239)⟩
end tm1_12_0

namespace tm1_12_1
noncomputable def realAnswer : RBox := ⟨14003077609328250276659862425,14003077609328253506323846104⟩
end tm1_12_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_13_0
noncomputable def realAnswer : RBox := ⟨101219952451832550639259265,101219952451832975246047237⟩
end tm0_13_0

namespace tm0_13_1
noncomputable def realAnswer : RBox := ⟨13348151488041610876325139171,13348151488041612676491950342⟩
end tm0_13_1

namespace tm1_13_0
noncomputable def realAnswer : RBox := ⟨(-561246532883464290960516956),(-561246532883463955480187060)⟩
end tm1_13_0

namespace tm1_13_1
noncomputable def realAnswer : RBox := ⟨(-11576117981336532936076796633),(-11576117981336531510972478193)⟩
end tm1_13_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_15_0
noncomputable def realAnswer : RBox := ⟨1994411597833863692036675106,1994411597833863798371202956⟩
end tm0_15_0

namespace tm0_15_1
noncomputable def realAnswer : RBox := ⟨4520813009778365385563538461,4520813009778365827963233574⟩
end tm0_15_1

namespace tm1_15_0
noncomputable def realAnswer : RBox := ⟨(-2008269166683526474670888816),(-2008269166683526401819601387)⟩
end tm1_15_0

namespace tm1_15_1
noncomputable def realAnswer : RBox := ⟨(-3110379647213410448229354670),(-3110379647213410142988937467)⟩
end tm1_15_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_16_0
noncomputable def realAnswer : RBox := ⟨(-1946190488131953152567737329),(-1946190488131953089559974081)⟩
end tm0_16_0

namespace tm0_16_1
noncomputable def realAnswer : RBox := ⟨(-505743175448926008538763736),(-505743175448925749649394073)⟩
end tm0_16_1

namespace tm1_16_0
noncomputable def realAnswer : RBox := ⟨1840104282087458721152872825,1840104282087458757292509302⟩
end tm1_16_0

namespace tm1_16_1
noncomputable def realAnswer : RBox := ⟨(-516248423913296423481711201),(-516248423913296273219142044)⟩
end tm1_16_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_19_0
noncomputable def realAnswer : RBox := ⟨295004157422964054342742445,295004157422964087604894869⟩
end tm0_19_0

namespace tm0_19_1
noncomputable def realAnswer : RBox := ⟨(-3744621698031936720374733436),(-3744621698031936588476595913)⟩
end tm0_19_1

namespace tm1_19_0
noncomputable def realAnswer : RBox := ⟨(-134823431526226154590683227),(-134823431526226145621867832)⟩
end tm1_19_0

namespace tm1_19_1
noncomputable def realAnswer : RBox := ⟨3750074270280003279286572535,3750074270280003314940020440⟩
end tm1_19_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_21_0
noncomputable def realAnswer : RBox := ⟨(-437074991101985873452234535),(-437074991101985840894798537)⟩
end tm0_21_0

namespace tm0_21_1
noncomputable def realAnswer : RBox := ⟨(-1933373948605254321659306977),(-1933373948605254193429801352)⟩
end tm0_21_1

namespace tm1_21_0
noncomputable def realAnswer : RBox := ⟨516186045157147345122968922,516186045157147351020799328⟩
end tm1_21_0

namespace tm1_21_1
noncomputable def realAnswer : RBox := ⟨1671830909317869721236382210,1671830909317869744315761751⟩
end tm1_21_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_24_0
noncomputable def realAnswer : RBox := ⟨341391337707192942157414601,341391337707192978967205097⟩
end tm0_24_0

namespace tm0_24_1
noncomputable def realAnswer : RBox := ⟨(-757173210817707749745198180),(-757173210817707605564306902)⟩
end tm0_24_1

namespace tm1_24_0
noncomputable def realAnswer : RBox := ⟨(-321116590488634535136753616),(-321116590488634530176962288)⟩
end tm1_24_0

namespace tm1_24_1
noncomputable def realAnswer : RBox := ⟨944332205628242195789116886,944332205628242214927529237⟩
end tm1_24_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_25_0
noncomputable def realAnswer : RBox := ⟨(-178371913017462713754173948),(-178371913017462674684038567)⟩
end tm0_25_0

namespace tm0_25_1
noncomputable def realAnswer : RBox := ⟨1000421245952386142342590616,1000421245952386295201412661⟩
end tm0_25_1

namespace tm1_25_0
noncomputable def realAnswer : RBox := ⟨145357274151593390435238464,145357274151593395614369484⟩
end tm1_25_0

namespace tm1_25_1
noncomputable def realAnswer : RBox := ⟨(-1114729848060612812633732209),(-1114729848060612792670197765)⟩
end tm1_25_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_27_0
noncomputable def realAnswer : RBox := ⟨75550970196554376321363745,75550970196554420317344378⟩
end tm0_27_0

namespace tm0_27_1
noncomputable def realAnswer : RBox := ⟨720553567884299650818083507,720553567884299822664925870⟩
end tm0_27_1

namespace tm1_27_0
noncomputable def realAnswer : RBox := ⟨(-107878477489568380761512951),(-107878477489568375471825680)⟩
end tm1_27_0

namespace tm1_27_1
noncomputable def realAnswer : RBox := ⟨(-710632828257853004647417914),(-710632828257852984258500169)⟩
end tm1_27_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_28_0
noncomputable def realAnswer : RBox := ⟨(-131481071073067977547785948),(-131481071073067931301417286)⟩
end tm0_28_0

namespace tm0_28_1
noncomputable def realAnswer : RBox := ⟨(-411055773262389004872630072),(-411055773262388824328019759)⟩
end tm0_28_1

namespace tm1_28_0
noncomputable def realAnswer : RBox := ⟨155572019941244826887539490,155572019941244831490224937⟩
end tm1_28_0

namespace tm1_28_1
noncomputable def realAnswer : RBox := ⟨364609029799472611920916555,364609029799472629685798941⟩
end tm1_28_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_3_0
noncomputable def realAnswer : RBox := ⟨32830528412365594735178805719,32830528412369375985991624890⟩
end tm0_3_0

namespace tm0_3_1
noncomputable def realAnswer : RBox := ⟨(-15618856502835542763768755812),(-15618856502819356540329828610)⟩
end tm0_3_1

namespace tm1_3_0
noncomputable def realAnswer : RBox := ⟨(-16488691250267850924605157438),(-16488691250264745126725223773)⟩
end tm1_3_0

namespace tm1_3_1
noncomputable def realAnswer : RBox := ⟨(-85975378650195094412669947185),(-85975378650181799632474642104)⟩
end tm1_3_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_31_0
noncomputable def realAnswer : RBox := ⟨78020444048585382531916179,78020444048585439335661606⟩
end tm0_31_0

namespace tm0_31_1
noncomputable def realAnswer : RBox := ⟨(-239534618261729968588487390),(-239534618261729747373073951)⟩
end tm0_31_1

namespace tm1_31_0
noncomputable def realAnswer : RBox := ⟨(-75495913527728390690869247),(-75495913527728385350286649)⟩
end tm1_31_0

namespace tm1_31_1
noncomputable def realAnswer : RBox := ⟨293337639947481856958050684,293337639947481877512287304⟩
end tm1_31_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_33_0
noncomputable def realAnswer : RBox := ⟨(-3044199428989143211349077),(-3044199428989078166392813)⟩
end tm0_33_0

namespace tm0_33_1
noncomputable def realAnswer : RBox := ⟨(-243976254038468075590530619),(-243976254038467822556038398)⟩
end tm0_33_1

namespace tm1_33_0
noncomputable def realAnswer : RBox := ⟨12215069927971731493248733,12215069927971736754551117⟩
end tm1_33_0

namespace tm1_33_1
noncomputable def realAnswer : RBox := ⟨261934818201327916583060461,261934818201327936862706164⟩
end tm1_33_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_36_0
noncomputable def realAnswer : RBox := ⟨37792790332170653145961062,37792790332170734284621373⟩
end tm0_36_0

namespace tm0_36_1
noncomputable def realAnswer : RBox := ⟨7993930541244689183994205,7993930541245004294663921⟩
end tm0_36_1

namespace tm1_36_0
noncomputable def realAnswer : RBox := ⟨(-42213343556155390425539910),(-42213343556155384463911185)⟩
end tm1_36_0

namespace tm1_36_1
noncomputable def realAnswer : RBox := ⟨8390938716962045111514656,8390938716962068086349959⟩
end tm1_36_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_37_0
noncomputable def realAnswer : RBox := ⟨(-29370582934653828919783223),(-29370582934653741360384559)⟩
end tm0_37_0

namespace tm0_37_1
noncomputable def realAnswer : RBox := ⟨45595938381698735995706285,45595938381699075866704275⟩
end tm0_37_1

namespace tm1_37_0
noncomputable def realAnswer : RBox := ⟨31150234651159119824220578,31150234651159126108273763⟩
end tm1_37_0

namespace tm1_37_1
noncomputable def realAnswer : RBox := ⟨(-63339289058750560672037176),(-63339289058750536455658540)⟩
end tm1_37_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_39_0
noncomputable def realAnswer : RBox := ⟨(-5664306510287534193931361),(-5664306510287432068379229)⟩
end tm0_39_0

namespace tm0_39_1
noncomputable def realAnswer : RBox := ⟨75602008855317509292897539,75602008855317905339733163⟩
end tm0_39_1

namespace tm1_39_0
noncomputable def realAnswer : RBox := ⟨3814879874588182261164540,3814879874588189129386526⟩
end tm1_39_0

namespace tm1_39_1
noncomputable def realAnswer : RBox := ⟨(-86372414523243464056214980),(-86372414523243437574240498)⟩
end tm1_39_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_4_0
noncomputable def realAnswer : RBox := ⟨(-27267351253595725533793942491),(-27267351253594410166593544319)⟩
end tm0_4_0

namespace tm0_4_1
noncomputable def realAnswer : RBox := ⟨50148790726984485973777225191,50148790726990412454157220070⟩
end tm0_4_1

namespace tm1_4_0
noncomputable def realAnswer : RBox := ⟨21103509700209855014884912917,21103509700210935407099364267⟩
end tm1_4_0

namespace tm1_4_1
noncomputable def realAnswer : RBox := ⟨4805922674105845575321751155,4805922674110713564699036015⟩
end tm1_4_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_40_0
noncomputable def realAnswer : RBox := ⟨(-3564742873703400419811456),(-3564742873703290051482128)⟩
end tm0_40_0

namespace tm0_40_1
noncomputable def realAnswer : RBox := ⟨(-61817586874970277100839556),(-61817586874969849266776777)⟩
end tm0_40_1

namespace tm1_40_0
noncomputable def realAnswer : RBox := ⟨6073463047078957344036214,6073463047078964452303204⟩
end tm1_40_0

namespace tm1_40_1
noncomputable def realAnswer : RBox := ⟨67331258355722050711189833,67331258355722078131629066⟩
end tm1_40_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_43_0
noncomputable def realAnswer : RBox := ⟨9945865136790413826693145,9945865136790554219258698⟩
end tm0_43_0

namespace tm0_43_1
noncomputable def realAnswer : RBox := ⟨(-3545413496681852633448877),(-3545413496681309078002377)⟩
end tm0_43_1

namespace tm1_43_0
noncomputable def realAnswer : RBox := ⟨(-11210826039410978593442721),(-11210826039410970123049447)⟩
end tm1_43_0

namespace tm1_43_1
noncomputable def realAnswer : RBox := ⟨8118584227224002811862307,8118584227224035496771760⟩
end tm1_43_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_45_0
noncomputable def realAnswer : RBox := ⟨3742783672198337321927855,3742783672198502670490069⟩
end tm0_45_0

namespace tm0_45_1
noncomputable def realAnswer : RBox := ⟨(-21217782321079061461896213),(-21217782321078421752966511)⟩
end tm0_45_1

namespace tm1_45_0
noncomputable def realAnswer : RBox := ⟨(-3625890911257070249543588),(-3625890911257060711477507)⟩
end tm1_45_0

namespace tm1_45_1
noncomputable def realAnswer : RBox := ⟨25556877822686968572379687,25556877822687005389577277⟩
end tm1_45_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_48_0
noncomputable def realAnswer : RBox := ⟨2832931920601157535470053,2832931920601369850790160⟩
end tm0_48_0

namespace tm0_48_1
noncomputable def realAnswer : RBox := ⟨8825365556067417432259549,8825365556068238025520023⟩
end tm0_48_1

namespace tm1_48_0
noncomputable def realAnswer : RBox := ⟨(-3536039430908912167965500),(-3536039430908900653753236)⟩
end tm1_48_0

namespace tm1_48_1
noncomputable def realAnswer : RBox := ⟨(-8983121047288311637854570),(-8983121047288267174037424)⟩
end tm1_48_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_49_0
noncomputable def realAnswer : RBox := ⟨(-3059575792570799333239946),(-3059575792570568288480499)⟩
end tm0_49_0

namespace tm0_49_1
noncomputable def realAnswer : RBox := ⟨(-2479952375768188910507557),(-2479952375767296208517596)⟩
end tm0_49_1

namespace tm1_49_0
noncomputable def realAnswer : RBox := ⟨3615278985555416750539577,3615278985555429066163844⟩
end tm1_49_0

namespace tm1_49_1
noncomputable def realAnswer : RBox := ⟨1664515711531349785274800,1664515711531397347255803⟩
end tm1_49_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_51_0
noncomputable def realAnswer : RBox := ⟨(-1699793845345938112936835),(-1699793845345664089615955)⟩
end tm0_51_0

namespace tm0_51_1
noncomputable def realAnswer : RBox := ⟨5200304166846744587568651,5200304166847802716798399⟩
end tm0_51_1

namespace tm1_51_0
noncomputable def realAnswer : RBox := ⟨1826671523696943567341146,1826671523696957704926722⟩
end tm1_51_0

namespace tm1_51_1
noncomputable def realAnswer : RBox := ⟨(-6627689147806205803865949),(-6627689147806151199823914)⟩
end tm1_51_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_52_0
noncomputable def realAnswer : RBox := ⟨746449516579172629605848,746449516579471251143110⟩
end tm0_52_0

namespace tm0_52_1
noncomputable def realAnswer : RBox := ⟨(-6039572021748288637954923),(-6039572021747135850322810)⟩
end tm0_52_1

namespace tm1_52_0
noncomputable def realAnswer : RBox := ⟨(-697663077359047168697648),(-697663077359032019404587)⟩
end tm1_52_0

namespace tm1_52_1
noncomputable def realAnswer : RBox := ⟨7249380535663368856712805,7249380535663427371653800⟩
end tm1_52_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_55_0
noncomputable def realAnswer : RBox := ⟨845453783418030537693047,845453783418418118138016⟩
end tm0_55_0

namespace tm0_55_1
noncomputable def realAnswer : RBox := ⟨1874181137083623556600243,1874181137085118558377618⟩
end tm0_55_1

namespace tm1_55_0
noncomputable def realAnswer : RBox := ⟨(-1043232539284810890500029),(-1043232539284792043765842)⟩
end tm1_55_0

namespace tm1_55_1
noncomputable def realAnswer : RBox := ⟨(-1875312459419055817506152),(-1875312459418983021787707)⟩
end tm1_55_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_57_0
noncomputable def realAnswer : RBox := ⟨652282074847596198590130,652282074848058284749828⟩
end tm0_57_0

namespace tm0_57_1
noncomputable def realAnswer : RBox := ⟨(-992906749645588748891919),(-992906749643807241148513)⟩
end tm0_57_1

namespace tm1_57_0
noncomputable def realAnswer : RBox := ⟨(-741238334734812021735111),(-741238334734790150506281)⟩
end tm1_57_0

namespace tm1_57_1
noncomputable def realAnswer : RBox := ⟨1386681053806310024095586,1386681053806394496918310⟩
end tm1_57_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_60_0
noncomputable def realAnswer : RBox := ⟨75971769218246777055318,75971769218850032574892⟩
end tm0_60_0

namespace tm0_60_1
noncomputable def realAnswer : RBox := ⟨1381364152997214247884518,1381364152999538405015276⟩
end tm0_60_1

namespace tm1_60_0
noncomputable def realAnswer : RBox := ⟨(-125803612545628195332682),(-125803612545600629354003)⟩
end tm1_60_0

namespace tm1_60_1
noncomputable def realAnswer : RBox := ⟨(-1595115118531336751111489),(-1595115118531230306571905)⟩
end tm1_60_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_61_0
noncomputable def realAnswer : RBox := ⟨(-200974869109375324946470),(-200974869108715552245045)⟩
end tm0_61_0

namespace tm0_61_1
noncomputable def realAnswer : RBox := ⟨(-888516151786157822168006),(-888516151783616475964583)⟩
end tm0_61_1

namespace tm1_61_0
noncomputable def realAnswer : RBox := ⟨261060996929422521804653,261060996929452346798378⟩
end tm1_61_0

namespace tm1_61_1
noncomputable def realAnswer : RBox := ⟨977166659463537830165871,977166659463652986612734⟩
end tm1_61_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_63_0
noncomputable def realAnswer : RBox := ⟨(-223038770277529706235140),(-223038770276739755324295)⟩
end tm0_63_0

namespace tm0_63_1
noncomputable def realAnswer : RBox := ⟨70081242392062904480595,70081242395104404632155⟩
end tm0_63_1

namespace tm1_63_0
noncomputable def realAnswer : RBox := ⟨263447283877477350180312,263447283877512342864946⟩
end tm1_63_0

namespace tm1_63_1
noncomputable def realAnswer : RBox := ⟨(-155555447508726620208529),(-155555447508591541373133)⟩
end tm1_63_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_64_0
noncomputable def realAnswer : RBox := ⟨161647718206797623535602,161647718207662394879231⟩
end tm0_64_0

namespace tm0_64_1
noncomputable def realAnswer : RBox := ⟨(-353316221860456044412642),(-353316221857127136258844)⟩
end tm0_64_1

namespace tm1_64_0
noncomputable def realAnswer : RBox := ⟨(-183714699146619880499357),(-183714699146581942178609)⟩
end tm1_64_0

namespace tm1_64_1
noncomputable def realAnswer : RBox := ⟨469586615601358086461855,469586615601504517864268⟩
end tm1_64_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_67_0
noncomputable def realAnswer : RBox := ⟨35431025228466764924054,35431025229603237429104⟩
end tm0_67_0

namespace tm0_67_1
noncomputable def realAnswer : RBox := ⟨349246520005742118643392,349246520010114431807693⟩
end tm0_67_1

namespace tm1_67_0
noncomputable def realAnswer : RBox := ⟨(-50769818354958454165441),(-50769818354909900704925)⟩
end tm1_67_0

namespace tm1_67_1
noncomputable def realAnswer : RBox := ⟨(-403271936299834283522632),(-403271936299646959759115)⟩
end tm1_67_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_69_0
noncomputable def realAnswer : RBox := ⟨68858341726846555624283,68858341728211923850640⟩
end tm0_69_0

namespace tm0_69_1
noncomputable def realAnswer : RBox := ⟨59879147803707497962469,59879147808958559828112⟩
end tm0_69_1

namespace tm1_69_0
noncomputable def realAnswer : RBox := ⟨(-83964659613487485024650),(-83964659613430077491778)⟩
end tm1_69_0

namespace tm1_69_1
noncomputable def realAnswer : RBox := ⟨(-50131342487055318958511),(-50131342486833904358666)⟩
end tm1_69_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_7_0
noncomputable def realAnswer : RBox := ⟨(-4861259750043649845753635642),(-4861259750043574982513025494)⟩
end tm0_7_0

namespace tm0_7_1
noncomputable def realAnswer : RBox := ⟨(-52055923391504402783180141630),(-52055923391504076410281457934)⟩
end tm0_7_1

namespace tm1_7_0
noncomputable def realAnswer : RBox := ⟨3335165413879492627614431909,3335165413879554122341923582⟩
end tm1_7_0

namespace tm1_7_1
noncomputable def realAnswer : RBox := ⟨39360419039382840483490021545,39360419039383108576504068635⟩
end tm1_7_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_72_0
noncomputable def realAnswer : RBox := ⟨(-17530653425248704571982),(-17530653423447372113713)⟩
end tm0_72_0

namespace tm0_72_1
noncomputable def realAnswer : RBox := ⟨136005507760620543305967,136005507767544798786493⟩
end tm0_72_1

namespace tm1_72_0
noncomputable def realAnswer : RBox := ⟨17988431131124676081898,17988431131198783728187⟩
end tm1_72_0

namespace tm1_72_1
noncomputable def realAnswer : RBox := ⟨(-167653798996250428905877),(-167653798995964745838420)⟩
end tm1_72_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_73_0
noncomputable def realAnswer : RBox := ⟨(-841742285119675924112),(-841742283143109135955)⟩
end tm0_73_0

namespace tm0_73_1
noncomputable def realAnswer : RBox := ⟨(-121522653073349174216943),(-121522653065752533929529)⟩
end tm0_73_1

namespace tm1_73_0
noncomputable def realAnswer : RBox := ⟨3760430488841473327422,3760430488922247256425⟩
end tm1_73_0

namespace tm1_73_1
noncomputable def realAnswer : RBox := ⟨145074853082426309364905,145074853082737637434032⟩
end tm1_73_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_75_0
noncomputable def realAnswer : RBox := ⟨(-18993541294188667113912),(-18993541291807259701266)⟩
end tm0_75_0

namespace tm0_75_1
noncomputable def realAnswer : RBox := ⟨(-43899099127471545339912),(-43899099118321768532223)⟩
end tm0_75_1

namespace tm1_75_0
noncomputable def realAnswer : RBox := ⟨23902436403953664456563,23902436404049760327700⟩
end tm1_75_0

namespace tm1_75_1
noncomputable def realAnswer : RBox := ⟨47141527175653376841867,47141527176023631676617⟩
end tm1_75_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_76_0
noncomputable def realAnswer : RBox := ⟨18950803974052993550276,18950803976667759663114⟩
end tm0_76_0

namespace tm0_76_1
noncomputable def realAnswer : RBox := ⟨5742032594533529965774,5742032604578425198662⟩
end tm0_76_1

namespace tm1_76_0
noncomputable def realAnswer : RBox := ⟨(-23028432096038812014293),(-23028432095933927040590)⟩
end tm1_76_0

namespace tm1_76_1
noncomputable def realAnswer : RBox := ⟨(-1477559346667933392636),(-1477559346263885275001)⟩
end tm1_76_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_79_0
noncomputable def realAnswer : RBox := ⟨(-3164539371572498060566),(-3164539368107102912051)⟩
end tm0_79_0

namespace tm0_79_1
noncomputable def realAnswer : RBox := ⟨38105410098656025132366,38105410111963069726088⟩
end tm0_79_1

namespace tm1_79_0
noncomputable def realAnswer : RBox := ⟨3024174298578441570867,3024174298715162126188⟩
end tm1_79_0

namespace tm1_79_1
noncomputable def realAnswer : RBox := ⟨(-46753404999480747608291),(-46753404998954337239478)⟩
end tm1_79_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_81_0
noncomputable def realAnswer : RBox := ⟨4471623370113257060231,4471623374298412838726⟩
end tm0_81_0

namespace tm0_81_1
noncomputable def realAnswer : RBox := ⟨20649971988373097609495,20649972004439736497656⟩
end tm0_81_1

namespace tm1_81_0
noncomputable def realAnswer : RBox := ⟨(-5862054526361836588495),(-5862054526198370689869)⟩
end tm1_81_0

namespace tm1_81_1
noncomputable def realAnswer : RBox := ⟨(-23693540032723797083618),(-23693540032094629911149)⟩
end tm1_81_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_84_0
noncomputable def realAnswer : RBox := ⟨(-3741968883730069035841),(-3741968878168129345637)⟩
end tm0_84_0

namespace tm0_84_1
noncomputable def realAnswer : RBox := ⟨7805982503628792511787,7805982524972812033643⟩
end tm0_84_1

namespace tm1_84_0
noncomputable def realAnswer : RBox := ⟨4397755827247444259971,4397755827461721764288⟩
end tm1_84_0

namespace tm1_84_1
noncomputable def realAnswer : RBox := ⟨(-10434463051771190634358),(-10434463050946878191820)⟩
end tm1_84_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_85_0
noncomputable def realAnswer : RBox := ⟨2025403830179276475764,2025403836296351287721⟩
end tm0_85_0

namespace tm0_85_1
noncomputable def realAnswer : RBox := ⟨(-10692958730927477677957),(-10692958707455933365734)⟩
end tm0_85_1

namespace tm1_85_0
noncomputable def realAnswer : RBox := ⟨(-2252967598195158789039),(-2252967597960493942003)⟩
end tm1_85_0

namespace tm1_85_1
noncomputable def realAnswer : RBox := ⟨13479474338649275048976,13479474339551864434065⟩
end tm1_85_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_87_0
noncomputable def realAnswer : RBox := ⟨(-761974749226097817126),(-761974741823450809776)⟩
end tm0_87_0

namespace tm0_87_1
noncomputable def realAnswer : RBox := ⟨(-8078233065995749792495),(-8078233037597981109889)⟩
end tm0_87_1

namespace tm1_87_0
noncomputable def realAnswer : RBox := ⟨1089873819768249424090,1089873820049954704908⟩
end tm1_87_0

namespace tm1_87_1
noncomputable def realAnswer : RBox := ⟨9602709033184702638402,9602709034267865112254⟩
end tm1_87_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_88_0
noncomputable def realAnswer : RBox := ⟨1416451901568151223034,1416451909713495051188⟩
end tm0_88_0

namespace tm0_88_1
noncomputable def realAnswer : RBox := ⟨4771590479890679237833,4771590511134050841236⟩
end tm0_88_1

namespace tm1_88_0
noncomputable def realAnswer : RBox := ⟨(-1823888486123148734616),(-1823888485814359790485)⟩
end tm1_88_0

namespace tm1_88_1
noncomputable def realAnswer : RBox := ⟨(-5431168394949166953021),(-5431168393762059591101)⟩
end tm1_88_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_9_0
noncomputable def realAnswer : RBox := ⟨(-8930787044774769828195039518),(-8930787044774757618910048919)⟩
end tm0_9_0

namespace tm0_9_1
noncomputable def realAnswer : RBox := ⟨(-7245594120479643888502411144),(-7245594120479591175414375579)⟩
end tm0_9_1

namespace tm1_9_0
noncomputable def realAnswer : RBox := ⟨7202028193925369475331878564,7202028193925379494336374573⟩
end tm1_9_0

namespace tm1_9_1
noncomputable def realAnswer : RBox := ⟨3904205633446939569043132619,3904205633446982828001763323⟩
end tm1_9_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_91_0
noncomputable def realAnswer : RBox := ⟨(-911177704393217940330),(-911177693532445976003)⟩
end tm0_91_0

namespace tm0_91_1
noncomputable def realAnswer : RBox := ⟨2581679115706842113257,2581679157352454382228⟩
end tm0_91_1

namespace tm1_91_0
noncomputable def realAnswer : RBox := ⟨1066334106485798835570,1066334106893166021489⟩
end tm1_91_0

namespace tm1_91_1
noncomputable def realAnswer : RBox := ⟨(-3368621437076543315075),(-3368621435511200598304)⟩
end tm1_91_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_93_0
noncomputable def realAnswer : RBox := ⟨926368537115562003,926381703513679349⟩
end tm0_93_0

namespace tm0_93_1
noncomputable def realAnswer : RBox := ⟨2797712088973146588678,2797712139449401449231⟩
end tm0_93_1

namespace tm1_93_0
noncomputable def realAnswer : RBox := ⟨(-53633112105657951957),(-53633111615012324371)⟩
end tm1_93_0

namespace tm1_93_1
noncomputable def realAnswer : RBox := ⟨(-3409850445954040140319),(-3409850444069261960749)⟩
end tm1_93_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments96
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_96_0
noncomputable def realAnswer : RBox := ⟨(-434569834362874084986),(-434569816771190187603)⟩
end tm0_96_0

namespace tm0_96_1
noncomputable def realAnswer : RBox := ⟨(-171121108253325606863),(-171121040831318688640)⟩
end tm0_96_1

namespace tm1_96_0
noncomputable def realAnswer : RBox := ⟨537041165872741861944,537041166522453474193⟩
end tm1_96_0

namespace tm1_96_1
noncomputable def realAnswer : RBox := ⟨105403726412580722875,105403728907318603959⟩
end tm1_96_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_97_0
noncomputable def realAnswer : RBox := ⟨347203367216128103220,347203386596589936645⟩
end tm0_97_0

namespace tm0_97_1
noncomputable def realAnswer : RBox := ⟨(-467188596558609880033),(-467188522287806434878)⟩
end tm0_97_1

namespace tm1_97_0
noncomputable def realAnswer : RBox := ⟨(-418372093776862426996),(-418372093063078192258)⟩
end tm1_97_0

namespace tm1_97_1
noncomputable def realAnswer : RBox := ⟨653205085450197881860,653205088190578558163⟩
end tm1_97_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments99
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_99_0
noncomputable def realAnswer : RBox := ⟨78904321776846285166,78904345307571969512⟩
end tm0_99_0

namespace tm0_99_1
noncomputable def realAnswer : RBox := ⟨(-872095526855242369576),(-872095436695804207035)⟩
end tm0_99_1

namespace tm1_99_0
noncomputable def realAnswer : RBox := ⟨(-81561402295561692950),(-81561401433505959113)⟩
end tm1_99_0

namespace tm1_99_1
noncomputable def realAnswer : RBox := ⟨1085856968718934528524,1085856972027670293609⟩
end tm1_99_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical
open IntegerIntervals
open scoped BigOperators
noncomputable def WplusBox : Matrix (Fin 6) (Fin 6) RBox := fun i j => RBox.rat (WplusInt i j) 10000
lemma WplusBox_contains (i j : Fin 6) : (WplusBox i j).Contains (Wplus i j) := RBox.contains_rat _ _ (by norm_num)
noncomputable def Aplus : Matrix (Fin 6) (Fin 6) ℝ := 1 - Dmat
noncomputable def AplusBox : Matrix (Fin 6) (Fin 6) RBox := fun i j => (RBox.rat (if i=j then 1 else 0) 1).add ((dEntries i j).neg)
noncomputable def defectplusBox : Matrix (Fin 6) (Fin 6) RBox := fun i j => (RBox.rat (if i=j then 1 else 0) 1).add ((matrixMulBox WplusBox AplusBox i j).neg)
noncomputable def WminusBox : Matrix (Fin 6) (Fin 6) RBox := fun i j => RBox.rat (WminusInt i j) 10000
lemma WminusBox_contains (i j : Fin 6) : (WminusBox i j).Contains (Wminus i j) := RBox.contains_rat _ _ (by norm_num)
noncomputable def Aminus : Matrix (Fin 6) (Fin 6) ℝ := 1 + Dmat
noncomputable def AminusBox : Matrix (Fin 6) (Fin 6) RBox := fun i j => (RBox.rat (if i=j then 1 else 0) 1).add ((dEntries i j))
noncomputable def defectminusBox : Matrix (Fin 6) (Fin 6) RBox := fun i j => (RBox.rat (if i=j then 1 else 0) 1).add ((matrixMulBox WminusBox AminusBox i j).neg)
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical.U12
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨12,by norm_num [residues]⟩
end SharpPlanar.Numerical.U12

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ENNReal
namespace SharpPlanar
section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  (e : ι → Node × Bool) (he : Function.Injective e)
  (f : κ → Node × Bool)
lemma compressed_S_matrix :
    (finiteRestriction e he).comp (S.comp (finiteEmbedding f)) =
      matrixL1 (fun i j => S (lp.single 1 (f j) 1) (e i)) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply,finiteRestriction_apply]
  change S (∑ j, lp.single 1 (f j) (x j)) (e i) = _
  rw [map_sum]
  simp only [lp.coeFn_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hs : (lp.single 1 (f j) (x j) : X) = (x j) • (lp.single 1 (f j) 1 : X) := by
    rw [← lp.single_smul]; simp
  rw [hs,map_smul]
  change x j * S (lp.single 1 (f j) 1) (e i) = S (lp.single 1 (f j) 1) (e i) * x j
  ring
end
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteFull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite interpolation system

Schur complements give existence, uniqueness and norm bounds for the finite system.
-/

namespace SharpPlanar.Numerical
noncomputable def signedS (neg : Bool) : X →L[ℝ] X := if neg then -S else S
noncomputable def signedU (neg : Bool) := RJ.comp ((signedS neg).comp IE)
noncomputable def signedE (neg : Bool) := RE.comp ((signedS neg).comp IE)
noncomputable def finiteA (neg : Bool) : L1Finite FiniteIndex →L[ℝ] L1Finite FiniteIndex :=
  1-RF.comp ((signedS neg).comp IF)
lemma compressed_D : RJ.comp (S.comp IJ) = matrixL1 Dmat := by
  rw [compressed_S_matrix]; rfl
end SharpPlanar.Numerical

end OAI
end


