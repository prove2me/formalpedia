-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0480_parallel1
-- name    : PNT_ZeroFree_433_0480_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:16:34.004383+00:00
-- url     : https://prove2.me/theorems/426fb19c-536b-4513-8af5-dbe5eed5566d
-- title:
--   Zero-free region foundations: Inversion.KernelSourceUniform [0480_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Inversion.KernelSourceUniform
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Inversion/KernelSourceUniform.lean#L11-L414

import Definitions.Def_PNT_ZeroFree_433_0003
import Definitions.Def_PNT_ZeroFree_433_0010
import Definitions.Def_PNT_ZeroFree_433_0035
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0052
import Definitions.Def_PNT_ZeroFree_433_0053
import Definitions.Def_PNT_ZeroFree_433_0059_1
import Definitions.Def_PNT_ZeroFree_433_0065_1
import Definitions.Def_PNT_ZeroFree_433_0145
import Definitions.Def_PNT_ZeroFree_433_0152
import Definitions.Def_PNT_ZeroFree_433_0154_parallel1
import Definitions.Def_PNT_ZeroFree_433_0188_parallel1
import Definitions.Def_PNT_ZeroFree_433_0250_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Inversion/KernelSourceUniform.lean#L11-L414
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Inversion.KernelSourceUniform
section
namespace OAI

namespace SevenEighths.InverseKernelSourceUniform

open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory LocalLogFourier
noncomputable section

def smallScalar (R : ℝ) : ℝ := min 1 (R ^ (1/4 : ℝ))

lemma smallScalar_pos {R : ℝ} (hR : 0 < R) : 0 < smallScalar R :=
  lt_min zero_lt_one (Real.rpow_pos_of_pos hR _)

def canonicalDensity (U : ℝ → ℂ) (V : 𝓢(ℝ, ℂ)) (R t : ℝ) : ℂ :=
  ((smallScalar R : ℝ) : ℂ)⁻¹ *
    (𝓕 (fun s : ℝ => U s * CubicReflectionKernel.paperKernel V (R * Real.exp s))) t

theorem paperKernel_window_source_bound (a b : ℝ) (ha : 0 < a) (K : ℕ) (L : ℝ) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ V : 𝓢(ℝ, ℂ), Function.support (V : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ R : ℝ, 0 < R → ∀ j ≤ K, ∀ s : ℝ, |s| ≤ L →
      ‖eulerDeriv (CubicReflectionKernel.paperKernel V) j (R * Real.exp s)‖ ≤
        C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V * smallScalar R := by
  choose orders c hc hb using fun j : Fin (K+1) =>
    CubicReflectionKernel.paperKernel_euler_source_power_decay a b ha 0 j.val
  let S := Finset.univ.biUnion orders
  let D := (∑ j : Fin (K+1), c j) + 1
  let E := (Real.exp L) ^ (1/4 : ℝ)
  have hD : 0 < D := by
    have hh := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin (K+1)))) => (hc j).le)
    dsimp only [D]
    linarith
  have hE : 0 < E := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hcD (j : Fin (K+1)) : c j ≤ D := by
    have hh := Finset.single_le_sum
      (fun q (_ : q ∈ (Finset.univ : Finset (Fin (K+1)))) => (hc q).le) (Finset.mem_univ j)
    dsimp only [D]
    linarith
  refine ⟨S, D*(1+E), by positivity, ?_⟩
  intro V hV R hR j hj s hs
  let Q := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  let q : Fin (K+1) := ⟨j, Nat.lt_succ_iff.mpr hj⟩
  have hsource : c q * (orders q).sup (schwartzSeminormFamily ℝ ℝ ℂ) V ≤ D*Q := by
    have hsub : orders q ⊆ S := Finset.subset_biUnion_of_mem orders (Finset.mem_univ q)
    exact mul_le_mul (hcD q) (Seminorm.le_def.mp (Finset.sup_mono hsub) V)
      (by positivity) hD.le
  have hsmall := (hb q V hV (R*Real.exp s) (mul_pos hR (Real.exp_pos _))).1
  have hlarge := (hb q V hV (R*Real.exp s) (mul_pos hR (Real.exp_pos _))).2
  have hsmall' : ‖eulerDeriv (CubicReflectionKernel.paperKernel V) j (R*Real.exp s)‖ ≤
      D*(1+E)*Q * R^(1/4 : ℝ) := by
    have he : (Real.exp s)^(1/4 : ℝ) ≤ E :=
      Real.rpow_le_rpow (by positivity) (Real.exp_le_exp.mpr ((le_abs_self s).trans hs)) (by norm_num)
    rw [Real.mul_rpow hR.le (Real.exp_pos _).le] at hsmall
    calc
      _ ≤ (c q * (orders q).sup (schwartzSeminormFamily ℝ ℝ ℂ) V) *
          (R^(1/4 : ℝ) * (Real.exp s)^(1/4 : ℝ)) := hsmall
      _ ≤ (D*Q) * (R^(1/4 : ℝ) * E) := mul_le_mul hsource
          (mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hR.le _)) (by positivity) (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hQ (Real.rpow_nonneg hR.le (1/4 : ℝ))]
  have hlarge' : ‖eulerDeriv (CubicReflectionKernel.paperKernel V) j (R*Real.exp s)‖ ≤ D*(1+E)*Q := by
    have hh : ‖eulerDeriv (CubicReflectionKernel.paperKernel V) j (R*Real.exp s)‖ ≤ D*Q := by
      apply (le_trans ?_ hsource)
      simpa only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] using hlarge
    exact hh.trans (by nlinarith [mul_nonneg (mul_nonneg hD.le hE.le) hQ])
  change _ ≤ D*(1+E)*Q * min 1 (R^(1/4 : ℝ))
  rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ D*(1+E)*Q), mul_one]
  exact le_min hlarge' hsmall'

private theorem localized_source_seminorm
    (V F : ℝ → ℂ) (R L CW CF : ℝ) (n k : ℕ)
    (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (hF : ContDiffOn ℝ ∞ F (Set.Ioi 0)) (hR : 0 < R)
    (hL : 0 ≤ L) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ n, ∀ s, ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s, (∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) → |s| ≤ L)
    (hEuler : ∀ i ≤ n, ∀ s, |s| ≤ L → ‖eulerDeriv F i (R * Real.exp s)‖ ≤ CF) :
    (SchwartzMap.seminorm ℝ k n) (positiveLogProfile V F R hVc hVs hF hR) ≤
      L ^ k * derivativeConstant n CW CF := by
  let g := positiveLogProfile V F R hVc hVs hF hR
  let G : ℝ → ℂ := fun z => F (R * Real.exp z)
  have hG : ContDiff ℝ ∞ G := by
    apply hF.comp_contDiff (by fun_prop)
    intro z
    exact mul_pos hR (Real.exp_pos _)
  have hgeq : (g : ℝ → ℂ) = fun z => V z * G z := by
    funext z
    exact positiveLogProfile_apply V F R z hVc hVs hF hR
  have hD : 0 ≤ derivativeConstant n CW CF := derivativeConstant_nonneg _ _ _ hCW hCF
  apply SchwartzMap.seminorm_le_bound' ℝ k n g (mul_nonneg (pow_nonneg hL _) hD)
  intro s
  have hprod := norm_iteratedFDeriv_mul_le hVs hG s (n := n) (by first | simp | exact_mod_cast le_top)
  by_cases hs : ∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0
  · have hwindow' := hwindow s hs
    have hraw : ‖iteratedDeriv n g s‖ ≤ derivativeConstant n CW CF := by
      rw [hgeq, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      apply hprod.trans
      unfold derivativeConstant
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hGi : ‖iteratedFDeriv ℝ (n - i) G s‖ ≤ CF := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, show (G : ℝ → ℂ) = fun z => F (R * Real.exp z) from rfl,
          iteratedDeriv_log_eq_euler]
        exact hEuler (n - i) (Nat.sub_le _ _) s hwindow'
      gcongr
      exact hVderiv i hi' s
    have hsk : ‖s‖ ^ k ≤ L ^ k := by simpa only [Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg s) hwindow' k
    exact mul_le_mul hsk hraw (norm_nonneg _) (pow_nonneg hL _)
  · have hz (i : ℕ) (hi : i ≤ n) : ‖iteratedFDeriv ℝ i V s‖ = 0 := by
      by_contra hne
      exact hs ⟨i, hi, hne⟩
    have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i V s‖ *
        ‖iteratedFDeriv ℝ (n - i) G s‖) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hz i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
      ring
    have hgzero : ‖iteratedDeriv n g s‖ = 0 := by
      rw [hgeq, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact le_antisymm (hprod.trans_eq hsum) (norm_nonneg _)
    rw [hgzero, mul_zero]
    positivity

theorem source_uniform_separation {ι : Type*} [Fintype ι]
    (a b : ℝ) (ha : 0 < a)
    (windows : ι → ℝ → ℂ) (slope M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hwindows : ∀ i y, windows i y ≠ 0 → |y| ≤ M i)
    (J : ℕ) :
    ∃ (U : ℝ → ℂ) (S : Finset (ℕ × ℕ)) (C : ℝ),
      0 ≤ C ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ V : 𝓢(ℝ, ℂ), Function.support (V : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ R : ℝ, 0 < R →
      (∀ y : ι → ℝ,
        (∏ i, windows i (y i)) * CubicReflectionKernel.paperKernel V
          (R * Real.exp (∑ i, slope i * y i)) =
        (smallScalar R : ℂ) * ∫ t : ℝ,
          (∏ i, windows i (y i) * FourierBridge.logPhase t (slope i * y i)) *
            canonicalDensity U V R t) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖)^J * ‖canonicalDensity U V R t‖) ∧
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖canonicalDensity U V R t‖) ≤
        C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V ∧
      (∀ t : ℝ, (1 + ‖t‖)^J * ‖canonicalDensity U V R t‖ ≤
        C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V) := by
  let T := ∑ i, |slope i| * M i
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hM i))
  let K := J + (volume : Measure ℝ).integrablePower
  let L := T+1
  have hL : 0 ≤ L := by dsimp only [L]; linarith
  obtain ⟨U, CW, hUc, hUs, hUone, hCW, hUderiv, hwindow⟩ :=
    FourierBridge.exists_complex_smooth_cutoff_with_derivative_bounds T K hT
  obtain ⟨S, CF, hCF, hkernel⟩ := paperKernel_window_source_bound a b ha K L
  let P0 := momentConstant K L CW CF
  let B0 := (2 : ℝ)^J * (FourierBridge.coefficientMomentBound 0 P0 +
    FourierBridge.coefficientMomentBound J P0)
  let B1 := FourierBridge.fourierPointBound J P0
  have hP0 : 0 ≤ P0 := momentConstant_nonneg K L CW CF hL hCW hCF.le
  have hB0 : 0 ≤ B0 := mul_nonneg (by positivity) (add_nonneg
    (FourierBridge.coefficientMomentBound_nonneg 0 P0 hP0)
    (FourierBridge.coefficientMomentBound_nonneg J P0 hP0))
  have hB1 : 0 ≤ B1 := FourierBridge.fourierPointBound_nonneg J P0 hP0
  refine ⟨U, S, B0+B1, add_nonneg hB0 hB1, hUc, hUs, ?_⟩
  intro V hV R hR
  let Q := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  let m := smallScalar R
  have hm : 0 < m := smallScalar_pos hR
  have hF := CubicReflectionKernel.paperKernel_compact_source_smooth V a b ha hV (V.smooth ⊤)
  let g := positiveLogProfile U (CubicReflectionKernel.paperKernel V) R hUc hUs hF hR
  let B : 𝓢(ℝ, ℂ) := ((m : ℂ)⁻¹) • (𝓕 g)
  have hcan (t : ℝ) : B t = canonicalDensity U V R t := by
    rfl
  have hnorm (t : ℝ) : ‖B t‖ = m⁻¹ * ‖(𝓕 g) t‖ := by
    simp only [B, smul_apply, smul_eq_mul, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
  have hP : 0 ≤ P0*Q := mul_nonneg hP0 hQ
  have hsource (n : ℕ) (hn : n ≤ K) : m⁻¹ *
      ((SchwartzMap.seminorm ℝ 0 n) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower n) g) ≤ P0*Q := by
    have hsemi (k : ℕ) : (SchwartzMap.seminorm ℝ k n) g ≤
        L^k * derivativeConstant n CW (CF*Q*m) := by
      apply localized_source_seminorm U (CubicReflectionKernel.paperKernel V)
        R L CW (CF*Q*m) n k hUc hUs hF hR hL hCW (by positivity)
      · intro i hi
        exact hUderiv i (hi.trans hn)
      · intro s hs
        exact (hwindow s (by obtain ⟨i, hi, hz⟩ := hs; exact ⟨i, hi.trans hn, hz⟩)).2.2
      · intro i hi s hs
        exact hkernel V hV R hR i (hi.trans hn) s hs
    have hd : derivativeConstant n CW (CF*Q*m) = derivativeConstant n CW CF * Q * m := by
      simp only [derivativeConstant, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hs : (SchwartzMap.seminorm ℝ 0 n) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower n) g ≤ (P0*Q)*m := by
      calc
        _ ≤ L^0 * derivativeConstant n CW (CF*Q*m) +
            L^(volume : Measure ℝ).integrablePower * derivativeConstant n CW (CF*Q*m) :=
          add_le_add (hsemi 0) (hsemi _)
        _ = ((1+L^(volume : Measure ℝ).integrablePower)*derivativeConstant n CW CF)*Q*m := by
          rw [hd]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (momentConstant_dominates K n L CW CF hL hCW hCF.le hn) hQ) hm.le
    exact (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hm.le)).trans_eq (by field_simp)
  have hB0Q : (2 : ℝ)^J * (FourierBridge.coefficientMomentBound 0 (P0*Q) +
      FourierBridge.coefficientMomentBound J (P0*Q)) = B0*Q := by
    dsimp only [B0]
    unfold FourierBridge.coefficientMomentBound
    ring
  have hB1Q : FourierBridge.fourierPointBound J (P0*Q) = B1*Q := by
    dsimp only [B1]
    unfold FourierBridge.fourierPointBound FourierBridge.fourierSeminormBound
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y
    have hactive : (∏ i, windows i (y i)) ≠ 0 → U (∑ i, slope i*y i) = 1 :=
      FourierBridge.coupled_cutoff_active windows U slope y M hwindows (by simpa [T] using hUone)
    have hsep := coupled_positive_log_separation windows (CubicReflectionKernel.paperKernel V)
      U R slope y hUc hUs hF hR hactive
    rw [hsep, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    rw [← hcan]
    dsimp only [B]
    simp only [smul_apply, smul_eq_mul]
    have hmC : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
    change _ = (m : ℂ)*_
    field_simp
    rfl
  · simp_rw [← hcan, hnorm]
    exact AnalyticBridge.schwartz_fourier_one_plus_integrable g J |>.const_mul m⁻¹ |>.congr
      (Filter.Eventually.of_forall (fun t => by dsimp only; ring))
  · simp_rw [← hcan, hnorm]
    have hh := FourierBridge.uniform_fourier_one_plus_moment g J m⁻¹ (P0*Q)
      (inv_nonneg.mpr hm.le) hP hsource
    rw [hB0Q] at hh
    have he : (∫ t : ℝ, (1+‖t‖)^J * (m⁻¹ * ‖(𝓕 g) t‖)) =
        m⁻¹ * ∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 g) t‖ := by
      simp_rw [← mul_assoc, mul_comm ((1+‖_‖)^J) m⁻¹, mul_assoc]
      rw [integral_const_mul]
    rw [he]
    exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB1) hQ)
  · intro t
    rw [← hcan, hnorm]
    have hh := FourierBridge.uniform_fourier_pointwise g J m⁻¹ (P0*Q)
      (inv_nonneg.mpr hm.le) hP (fun i hi => hsource i (hi.trans (by dsimp only [K]; omega))) t
    rw [hB1Q] at hh
    have he : (1+‖t‖)^J*(m⁻¹*‖(𝓕 g) t‖) = m⁻¹*(1+‖t‖)^J*‖(𝓕 g) t‖ := by ring
    rw [he]
    exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB0) hQ)

def twistedDensity (U W : ℝ → ℂ) (θ R t : ℝ) : ℂ :=
  (smallScalar R : ℂ)⁻¹ *
    (𝓕 (fun s : ℝ => U s * CubicReflectionKernel.paperKernel
      (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ)) (R * Real.exp s))) t

theorem normTwistedSource_uniform_separation {ι : Type*} [Fintype ι]
    (a b : ℝ) (ha : 0 < a)
    (windows : ι → ℝ → ℂ) (slope M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hwindows : ∀ i y, windows i y ≠ 0 → |y| ≤ M i)
    (W : ℝ → ℂ) (hsupp : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ → ℂ) (n : ℕ) (C : ℝ),
      0 ≤ C ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ θ R : ℝ, 0 < R →
      (∀ y : ι → ℝ,
        (∏ i, windows i (y i)) * CubicReflectionKernel.paperKernel
          (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ))
          (R * Real.exp (∑ i, slope i * y i)) =
        (smallScalar R : ℂ) * ∫ t : ℝ,
          (∏ i, windows i (y i) * FourierBridge.logPhase t (slope i * y i)) *
            twistedDensity U W θ R t) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖)^J * ‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖twistedDensity U W θ R t‖) ≤ C * (1 + ‖θ‖)^n ∧
      (∀ t : ℝ, (1 + ‖t‖)^J * ‖twistedDensity U W θ R t‖ ≤ C * (1 + ‖θ‖)^n) := by
  obtain ⟨U, orders, C, hC, hUc, hUs, hsep⟩ :=
    source_uniform_separation a b ha windows slope M hM hwindows J
  let V := CompletedGauss.vstarSchwartz W a b ha hsupp hW
  have hV : Function.support (V : ℝ → ℂ) ⊆ Set.Icc a b :=
    CompletedGauss.Vstar_support W a b hsupp
  obtain ⟨G, hG, hbound⟩ := CompletedHeight.normTwistedSource_schwartz V a b ha hV
  have hlink (θ : ℝ) : (G θ : ℝ → ℂ) =
      CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ) := by
    funext x
    rw [hG θ x]
    change FourierBridge.logPhase θ (Real.log x)*((Real.sqrt x:ℂ)*W x) =
      (Real.sqrt x:ℂ)*(FourierBridge.logPhase θ (Real.log x)*W x)
    ring
  have hGs (θ : ℝ) : Function.support (G θ : ℝ → ℂ) ⊆ Set.Icc a b := by
    intro x hx
    change G θ x ≠ 0 at hx
    rw [hG θ x] at hx
    exact hV (CompletedHeight.normTwistedSource_support V θ hx)
  obtain ⟨n, D, hD, hpoly⟩ := hbound orders
  refine ⟨U, n, C*D, mul_nonneg hC hD.le, hUc, hUs, ?_⟩
  intro θ R hR
  have hcan : canonicalDensity U (G θ) R = twistedDensity U W θ R := by
    unfold canonicalDensity twistedDensity
    rw [hlink θ]
  obtain ⟨heq, hi, hm, hp⟩ := hsep (G θ) (hGs θ) R hR
  rw [hcan] at heq hi hm hp
  rw [hlink θ] at heq
  have hb : C * orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G θ) ≤
      C*D * (1+‖θ‖)^n :=
    (mul_le_mul_of_nonneg_left (hpoly θ) hC).trans_eq (by ring)
  exact ⟨heq, hi, hm.trans hb, fun t => (hp t).trans hb⟩

theorem fourier_joint_stronglyMeasurable {α : Type*} [MeasurableSpace α]
    (f : α → ℝ → ℂ) (hf : StronglyMeasurable (Function.uncurry f)) :
    StronglyMeasurable (fun p : α × ℝ => (𝓕 (f p.1)) p.2) := by
  simp_rw [Real.fourier_eq']
  apply StronglyMeasurable.integral_prod_right
  have he : Continuous (fun p : ℝ × ℝ =>
      Complex.exp ((↑(-2 * Real.pi * inner ℝ p.1 p.2) : ℂ) * Complex.I)) := by
    fun_prop
  exact (he.stronglyMeasurable.comp_measurable
    (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).smul
    (hf.comp_measurable ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

theorem paperKernel_joint_stronglyMeasurable {α : Type*} [MeasurableSpace α]
    (a b : ℝ) (ha : 0 < a) (V : α → 𝓢(ℝ, ℂ))
    (hV : ∀ θ, Function.support (V θ : ℝ → ℂ) ⊆ Set.Icc a b)
    (hf : StronglyMeasurable (fun p : α × ℝ => V p.1 (Real.exp p.2))) :
    StronglyMeasurable (fun p : α × Set.Ioi (0 : ℝ) =>
      CubicReflectionKernel.paperKernel (V p.1) p.2) := by
  let f : α → ℝ → ℂ := fun θ s => V θ (Real.exp s)
  let g : α → ℝ → ℂ := fun θ u => CubicReflectionKernel.axisMultiplier u * (𝓕 (f θ)) u
  have hfF := fourier_joint_stronglyMeasurable f hf
  have hg : StronglyMeasurable (Function.uncurry g) :=
    (CubicReflectionKernel.axisMultiplier_continuous.stronglyMeasurable.comp_measurable
      measurable_snd).mul hfF
  have hgF := fourier_joint_stronglyMeasurable g hg
  have harg : Measurable (fun p : α × Set.Ioi (0 : ℝ) =>
      (p.1, Real.log (CubicReflectionKernel.paperScale * (p.2 : ℝ)))) :=
    measurable_fst.prodMk (Real.measurable_log.comp
      (measurable_const.mul (measurable_subtype_coe.comp measurable_snd)))
  convert! hgF.comp_measurable harg using 1
  funext p
  let L := CubicReflectionKernel.logSchwartz (V p.1) a b ha (hV p.1) ((V p.1).smooth ⊤)
  exact CubicReflectionKernel.paperKernel_eq_logFourier (V p.1) L
    (fun _ => rfl) p.2 p.2.property

private theorem twistedDensity_measurable_of_profile
    (U W : ℝ → ℂ) (R : ℝ)
    (hprofile : StronglyMeasurable (fun p : ℝ × ℝ =>
      U p.2 * CubicReflectionKernel.paperKernel
        (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W p.1)) (R * Real.exp p.2))) :
    StronglyMeasurable (fun p : ℝ × ℝ => twistedDensity U W p.1 R p.2) := by
  unfold twistedDensity
  exact stronglyMeasurable_const.mul (fourier_joint_stronglyMeasurable
    (fun θ s => U s * CubicReflectionKernel.paperKernel
      (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ)) (R * Real.exp s)) hprofile)

private theorem exists_measurable_twisted_source
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃ G : ℝ → 𝓢(ℝ, ℂ),
      (∀ θ, (G θ : ℝ → ℂ) = CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ)) ∧
      (∀ θ, Function.support (G θ : ℝ → ℂ) ⊆ Set.Icc a b) ∧
      StronglyMeasurable (fun p : ℝ × ℝ => G p.1 (Real.exp p.2)) := by
  let V := CompletedGauss.vstarSchwartz W a b ha hsupp hW
  have hV : Function.support (V : ℝ → ℂ) ⊆ Set.Icc a b :=
    CompletedGauss.Vstar_support W a b hsupp
  obtain ⟨G, hG, _⟩ := CompletedHeight.normTwistedSource_schwartz V a b ha hV
  have hlink (θ : ℝ) : (G θ : ℝ → ℂ) =
      CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ) := by
    funext x
    rw [hG θ x]
    change FourierBridge.logPhase θ (Real.log x)*((Real.sqrt x:ℂ)*W x) =
      (Real.sqrt x:ℂ)*(FourierBridge.logPhase θ (Real.log x)*W x)
    ring
  have hGs (θ : ℝ) : Function.support (G θ : ℝ → ℂ) ⊆ Set.Icc a b := by
    intro x hx
    change G θ x ≠ 0 at hx
    rw [hG θ x] at hx
    exact hV (CompletedHeight.normTwistedSource_support V θ hx)
  have hf : StronglyMeasurable (fun p : ℝ × ℝ => G p.1 (Real.exp p.2)) := by
    simp_rw [hG, CompletedHeight.normTwistedSource, Real.log_exp]
    apply Continuous.stronglyMeasurable
    unfold FourierBridge.logPhase
    exact (by fun_prop : Continuous (fun p : ℝ × ℝ =>
      Complex.exp ((↑(2*Real.pi*p.1*p.2) : ℂ)*Complex.I))).mul
      (V.continuous.comp (Real.continuous_exp.comp continuous_snd))
  exact ⟨G, hlink, hGs, hf⟩

theorem twistedDensity_joint_stronglyMeasurable
    (U W : ℝ → ℂ) (hU : Measurable U)
    (a b : ℝ) (ha : 0 < a) (hsupp : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (R : ℝ) (hR : 0 < R) :
    StronglyMeasurable (fun p : ℝ × ℝ => twistedDensity U W p.1 R p.2) := by
  obtain ⟨G, hlink, hGs, hf⟩ := exists_measurable_twisted_source W a b ha hsupp hW
  have hkernel := paperKernel_joint_stronglyMeasurable a b ha G hGs hf
  have harg : Measurable (fun p : ℝ × ℝ =>
      (p.1, (⟨R * Real.exp p.2, mul_pos hR (Real.exp_pos _)⟩ : Set.Ioi (0 : ℝ)))) :=
    measurable_fst.prodMk ((measurable_const.mul (Real.measurable_exp.comp measurable_snd)).subtype_mk)
  have hcomposed := hkernel.comp_measurable harg
  change StronglyMeasurable (fun p : ℝ × ℝ =>
    CubicReflectionKernel.paperKernel (G p.1) (R * Real.exp p.2)) at hcomposed
  have hprofile : StronglyMeasurable (fun p : ℝ × ℝ =>
      U p.2 * CubicReflectionKernel.paperKernel
        (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W p.1)) (R*Real.exp p.2)) := by
    have hprofileG : StronglyMeasurable (fun p : ℝ × ℝ =>
        U p.2 * CubicReflectionKernel.paperKernel (G p.1) (R * Real.exp p.2)) :=
      (hU.stronglyMeasurable.comp_measurable measurable_snd).mul
        hcomposed
    convert! hprofileG using 1
    exact funext (fun p => congrArg
      (fun V : ℝ → ℂ => U p.2 * CubicReflectionKernel.paperKernel V (R * Real.exp p.2))
      (hlink p.1).symm)
  exact twistedDensity_measurable_of_profile U W R hprofile

end
end SevenEighths.InverseKernelSourceUniform

end OAI

end


