-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0053
-- name    : PNT_ZeroFree_433_0053
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T15:21:45.036642+00:00
-- url     : https://prove2.me/theorems/cabbf1c2-fea3-48b9-a861-374419b5c8f9
-- title:
--   Zero-free region foundations: Mellin.ReflectedKernel [0053]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Mellin.ReflectedKernel
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Mellin/ReflectedKernel.lean#L78-L614

import Definitions.Def_PNT_ZeroFree_433_0052

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Mellin/ReflectedKernel.lean#L78-L614
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Mellin.ReflectedKernel
section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

namespace CubicReflectionKernel

section
open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory

theorem reflectedLogProfile_deriv_bound (logSource : SchwartzMap ℝ ℂ) (j : ℕ) (y : ℝ) :
    ‖iteratedDeriv j (reflectedLogProfile logSource) y‖ ≤
      (2 * Real.pi) ^ j * ∫ u : ℝ, ‖u‖ ^ j * ‖(𝓕 logSource) u‖ := by
  rw [reflectedLogProfile_deriv]
  have hb := VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ ℝ)
    (fun u : ℝ => (-2 * Real.pi * Complex.I * u) ^ j * spectralProfile logSource u) y
  change ‖𝓕 (fun u : ℝ => (-2 * Real.pi * Complex.I * u) ^ j * spectralProfile logSource u) y‖ ≤ _ at hb
  refine hb.trans_eq ?_
  have hnorm (u : ℝ) :
      ‖(-2 * Real.pi * Complex.I * u) ^ j * spectralProfile logSource u‖ =
        (2 * Real.pi) ^ j * (‖u‖ ^ j * ‖(𝓕 logSource) u‖) := by
    simp only [norm_mul, norm_pow, spectralProfile_norm, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  simp_rw [hnorm]
  exact integral_const_mul _ _

def momentScale : ℝ :=
  2 ^ (volume : Measure ℝ).integrablePower *
    ∫ u : ℝ, (1 + ‖u‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)

theorem momentScale_nonneg : 0 ≤ momentScale := by
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro u
  positivity

theorem reflectedLogProfile_source_bound (j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (logSource : SchwartzMap ℝ ℂ) (y : ℝ),
        ‖iteratedDeriv j (reflectedLogProfile logSource) y‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource := by
  let m := j + (volume : Measure ℝ).integrablePower
  let S : Finset (ℕ × ℕ) := {(0, 0), (m, 0)}
  obtain ⟨s, C, hC, hbound⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control (E := ℝ)
    (FourierTransform.fourierCLM ℝ (SchwartzMap ℝ ℂ)) S
  refine ⟨s, (2 * Real.pi) ^ j * (momentScale + 1) * (2 * C), by
    have := momentScale_nonneg
    positivity, ?_⟩
  intro logSource y
  have h0' : schwartzSeminormFamily ℝ ℝ ℂ (0, 0) ≤
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
    Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ) (by simp [S])
  have hm' : schwartzSeminormFamily ℝ ℝ ℂ (m, 0) ≤
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
    Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ) (by simp [S])
  have h0 := Seminorm.le_def.mp h0' (𝓕 logSource)
  have hm := Seminorm.le_def.mp hm' (𝓕 logSource)
  change SchwartzMap.seminorm ℝ 0 0 (𝓕 logSource) ≤ _ at h0
  change SchwartzMap.seminorm ℝ m 0 (𝓕 logSource) ≤ _ at hm
  have hs := hbound logSource
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (𝓕 logSource) ≤ _ at hs
  have hsum : SchwartzMap.seminorm ℝ 0 0 (𝓕 logSource) + SchwartzMap.seminorm ℝ m 0 (𝓕 logSource) ≤
      2 * C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource := by linarith
  have hmoment := FourierBridge.fourier_coefficient_moment logSource j
  change (∫ u : ℝ, ‖u‖ ^ j * ‖(𝓕 logSource) u‖) ≤ momentScale *
    (SchwartzMap.seminorm ℝ 0 0 (𝓕 logSource) + SchwartzMap.seminorm ℝ m 0 (𝓕 logSource)) at hmoment
  calc
    _ ≤ (2 * Real.pi) ^ j * ∫ u : ℝ, ‖u‖ ^ j * ‖(𝓕 logSource) u‖ :=
      reflectedLogProfile_deriv_bound logSource j y
    _ ≤ (2 * Real.pi) ^ j * (momentScale *
        (2 * C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource)) := by
      exact mul_le_mul_of_nonneg_left
        (hmoment.trans (mul_le_mul_of_nonneg_left hsum momentScale_nonneg)) (by positivity)
    _ ≤ _ := by
      have hpos : 0 ≤ 2 * C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource := by positivity
      calc
        _ ≤ (2 * Real.pi) ^ j * ((momentScale + 1) *
            (2 * C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right zero_le_one) hpos) (by positivity)
        _ = _ := by ring

end

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Asymptotics

def paperScale : ℝ := (2 * Real.pi) ^ 4 / 27

theorem paperScale_pos : 0 < paperScale := by
  unfold paperScale
  positivity

def paperKernel (V : ℝ → ℂ) (x : ℝ) : ℂ :=
  mellinInv 0 (fun t => mellin V (-t) * gammaMultiplier t) (paperScale * x)

theorem logProfile_compact (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) :
    HasCompactSupport (fun u : ℝ => V (Real.exp u)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (Real.log a) (Real.log b)) isCompact_Icc
  intro u hu
  have huv : V (Real.exp u) ≠ 0 := hu
  have hm := hsupp huv
  constructor
  · simpa only [Real.log_exp] using Real.log_le_log ha hm.1
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos u) hm.2

def logSchwartz (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) :
    SchwartzMap ℝ ℂ :=
  (logProfile_compact V a b ha hsupp).toSchwartzMap (hV.comp Real.contDiff_exp)

@[simp] theorem logSchwartz_apply (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) (u : ℝ) :
    logSchwartz V a b ha hsupp hV u = V (Real.exp u) := rfl

theorem compact_source_mellin_convergent
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) : MellinConvergent V s := by
  have hlocal : LocallyIntegrableOn V (Set.Ioi (0 : ℝ)) :=
    hV.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htopzero : V =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_gt_atTop b] with y hy
    by_contra hn
    exact (not_le_of_gt hy) (hsupp hn).2
  have hbotzero : V =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    by_contra hn
    exact (not_le_of_gt hy.2) (hsupp hn).1
  have htop : V =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) :=
    htopzero.isBigO.trans (isBigO_zero _ _)
  have hbot : V =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(s.re - 1))) :=
    hbotzero.isBigO.trans (isBigO_zero _ _)
  exact mellinConvergent_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)

theorem mellin_axis_eq_fourier (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (u : ℝ) :
    mellin V (-((2 * Real.pi * u : ℝ) * Complex.I)) = (𝓕 logSource) u := by
  rw [mellin_eq_fourier]
  have hfreq : (-((2 * Real.pi * u : ℝ) * Complex.I) : ℂ).im / (2 * Real.pi) = -u := by
    simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
    field_simp
  rw [hfreq]
  have hfun : (fun v : ℝ => Real.exp
      (-(-((2 * Real.pi * u : ℝ) * Complex.I) : ℂ).re * v) • V (Real.exp (-v))) =
      (logSource : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ := by
    funext v
    simp [hL]
  rw [hfun, Real.fourier_comp_linearIsometry]
  simp
  rfl

theorem paperKernel_eq_logFourier (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (x : ℝ) (hx : 0 < x) :
    paperKernel V x = reflectedLogProfile logSource (Real.log (paperScale * x)) := by
  unfold paperKernel
  rw [mellinInv_eq_fourierInv 0 _ (mul_pos paperScale_pos hx)]
  simp only [Complex.ofReal_zero, neg_zero, Complex.cpow_zero, one_smul]
  rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  have hfun : (fun y : ℝ => mellin V (-(0 + 2 * Real.pi * y * Complex.I)) *
      gammaMultiplier (0 + 2 * Real.pi * y * Complex.I)) = spectralProfile logSource := by
    funext y
    have hy : (0 + 2 * Real.pi * y * Complex.I : ℂ) =
        ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hy, mellin_axis_eq_fourier V logSource hL]
    exact mul_comm _ _
  rw [hfun]
  rfl

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter
namespace CubicReflectionKernel

theorem kernel_vertical_eq_spectralProfile (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (y : ℝ) :
    mellin V (-(y * Complex.I)) * gammaMultiplier (y * Complex.I) =
      spectralProfile logSource (y / (2 * Real.pi)) := by
  have hy : 2 * Real.pi * (y / (2 * Real.pi)) = y := by field_simp
  rw [spectralProfile, axisMultiplier, ← mellin_axis_eq_fourier V logSource hL, hy]
  exact mul_comm _ _

theorem kernel_vertical_integrable (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) :
    Complex.VerticalIntegrable (fun t => mellin V (-t) * gammaMultiplier t) 0 := by
  have hi : Integrable (spectralProfile logSource) := by
    simpa using spectralProfile_pow_integrable logSource 0
  have hscaled := hi.comp_div (R := 2 * Real.pi) (by positivity)
  simpa only [Complex.VerticalIntegrable, Complex.ofReal_zero, zero_add,
    kernel_vertical_eq_spectralProfile V logSource hL] using hscaled

theorem paperKernel_integrable (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (x : ℝ) (hx : 0 < x) :
    Integrable (fun y : ℝ => ((paperScale * x : ℝ) : ℂ) ^ (-(y * Complex.I)) *
      (mellin V (-(y * Complex.I)) * gammaMultiplier (y * Complex.I))) := by
  have hcx := mul_pos paperScale_pos hx
  have hi := kernel_vertical_integrable V logSource hL
  simp only [Complex.VerticalIntegrable, Complex.ofReal_zero, zero_add] at hi
  apply hi.bdd_mul (c := 1)
  · exact ((show Continuous (fun y : ℝ => -(y * Complex.I)) by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt hcx)))).aestronglyMeasurable
  · filter_upwards [] with y
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hcx]
    simp

theorem paperKernel_contDiffOn (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) :
    ContDiffOn ℝ ∞ (paperKernel V) (Set.Ioi 0) := by
  have hg : ContDiffOn ℝ ∞
      (fun x => reflectedLogProfile logSource (Real.log (paperScale * x))) (Set.Ioi 0) := by
    intro x hx
    apply (reflectedLogProfile_smooth logSource).contDiffAt.comp_contDiffWithinAt x
    exact ((contDiffAt_const.mul contDiffAt_id).log
      (ne_of_gt (mul_pos paperScale_pos hx))).contDiffWithinAt
  apply hg.congr
  intro x hx
  exact paperKernel_eq_logFourier V logSource hL x hx

theorem paperKernel_euler_eq (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (j : ℕ) (x : ℝ) (hx : 0 < x) :
    LocalLogFourier.eulerDeriv (paperKernel V) j x =
      iteratedDeriv j (reflectedLogProfile logSource) (Real.log (paperScale * x)) := by
  have hfun : (fun t : ℝ => paperKernel V (x * Real.exp t)) =
      (fun t : ℝ => reflectedLogProfile logSource (Real.log (paperScale * x) + t)) := by
    funext t
    rw [paperKernel_eq_logFourier V logSource hL _ (mul_pos hx (Real.exp_pos t))]
    rw [← mul_assoc, Real.log_mul (ne_of_gt (mul_pos paperScale_pos hx))
      (ne_of_gt (Real.exp_pos t)), Real.log_exp]
  rw [LocalLogFourier.eulerDeriv, hfun, iteratedDeriv_comp_const_add]
  simp

theorem paperKernel_source_euler_bound (j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
        (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
        (x : ℝ), 0 < x →
        ‖LocalLogFourier.eulerDeriv (paperKernel V) j x‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (logSchwartz V a b ha hsupp hV) := by
  obtain ⟨s, C, hC, hb⟩ := reflectedLogProfile_source_bound j
  refine ⟨s, C, hC, ?_⟩
  intro V a b ha hsupp hV x hx
  rw [paperKernel_euler_eq V (logSchwartz V a b ha hsupp hV) (by intro u; rfl) j x hx]
  exact hb _ _

theorem paperKernel_compact_source_integrable
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (x : ℝ) (hx : 0 < x) :
    Integrable (fun y : ℝ => ((paperScale * x : ℝ) : ℂ) ^ (-(y * Complex.I)) *
      (mellin V (-(y * Complex.I)) * gammaMultiplier (y * Complex.I))) :=
  paperKernel_integrable V (logSchwartz V a b ha hsupp hV) (by intro u; rfl) x hx

theorem paperKernel_compact_source_smooth
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) :
    ContDiffOn ℝ ∞ (paperKernel V) (Set.Ioi 0) :=
  paperKernel_contDiffOn V (logSchwartz V a b ha hsupp hV) (by intro u; rfl)

theorem reflectedLogProfile_deriv_vanish (logSource : SchwartzMap ℝ ℂ) (j : ℕ) :
    Tendsto (iteratedDeriv j (reflectedLogProfile logSource)) (cocompact ℝ) (𝓝 0) := by
  rw [reflectedLogProfile_deriv]
  exact Real.zero_at_infty_fourier _

theorem paperKernel_euler_vanish_infty (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (j : ℕ) :
    Tendsto (LocalLogFourier.eulerDeriv (paperKernel V) j) atTop (𝓝 0) := by
  have hd := (reflectedLogProfile_deriv_vanish logSource j).mono_left atTop_le_cocompact
  have hlog : Tendsto (fun x : ℝ => Real.log (paperScale * x)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Tendsto.const_mul_atTop paperScale_pos tendsto_id)
  apply (hd.comp hlog).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (paperKernel_euler_eq V logSource hL j x hx).symm

theorem paperKernel_euler_vanish_zero (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (j : ℕ) :
    Tendsto (LocalLogFourier.eulerDeriv (paperKernel V) j) (𝓝[>] 0) (𝓝 0) := by
  have hd := (reflectedLogProfile_deriv_vanish logSource j).mono_left atBot_le_cocompact
  have hmul : Tendsto (fun x : ℝ => paperScale * x) (𝓝[>] 0) (𝓝[>] 0) := by
    have hm : Tendsto (fun x : ℝ => paperScale * x)
        (comap (fun x : ℝ => paperScale * x) (𝓝[>] 0)) (𝓝[>] 0) := tendsto_comap
    rwa [comap_mulLeft_nhdsGT_zero paperScale_pos] at hm
  have hlog := Real.tendsto_log_nhdsGT_zero.comp hmul
  apply (hd.comp hlog).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (paperKernel_euler_eq V logSource hL j x hx).symm

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Asymptotics

theorem compact_source_mellin_hasDerivAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) :
    HasDerivAt (mellin V) (mellin (fun t => Real.log t • V t) s) s := by
  have hlocal : LocallyIntegrableOn V (Set.Ioi (0 : ℝ)) :=
    hV.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htopzero : V =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_gt_atTop b] with y hy
    by_contra hn
    exact (not_le_of_gt hy) (hsupp hn).2
  have hbotzero : V =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    by_contra hn
    exact (not_le_of_gt hy.2) (hsupp hn).1
  have htop : V =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) :=
    htopzero.isBigO.trans (isBigO_zero _ _)
  have hbot : V =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(s.re - 1))) :=
    hbotzero.isBigO.trans (isBigO_zero _ _)
  exact (mellin_hasDerivAt_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)).2

theorem compact_source_mellin_differentiable
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) :
    Differentiable ℂ (mellin V) :=
  fun s => (compact_source_mellin_hasDerivAt V a b ha hsupp hV s).differentiableAt

theorem Gamma_differentiableAt_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.Gamma z := by
  apply Complex.differentiableAt_Gamma
  intro m hm
  have hr := congrArg Complex.re hm
  simp only [Complex.neg_re, Complex.natCast_re] at hr
  have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem gammaMultiplier_differentiableAt (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ gammaMultiplier s := by
  have h1 := (Gamma_differentiableAt_of_re_pos ((7 / 6 : ℂ) + s) (by
    norm_num [Complex.add_re, Complex.div_re]
    linarith)).comp s (differentiableAt_const _ |>.add differentiableAt_id)
  have h2 := (Gamma_differentiableAt_of_re_pos ((5 / 6 : ℂ) + s) (by
    norm_num [Complex.add_re, Complex.div_re]
    linarith)).comp s (differentiableAt_const _ |>.add differentiableAt_id)
  have h3 := (Complex.differentiable_one_div_Gamma ((7 / 6 : ℂ) - s)).comp s
    (differentiableAt_const _ |>.sub differentiableAt_id)
  have h4 := (Complex.differentiable_one_div_Gamma ((5 / 6 : ℂ) - s)).comp s
    (differentiableAt_const _ |>.sub differentiableAt_id)
  convert! ((h1.mul h2).mul (h3.mul h4)) using 1
  ext z
  simp only [gammaMultiplier, Function.comp_def, div_eq_mul_inv, mul_inv_rev, Pi.mul_apply]
  ring

theorem kernelMellinIntegrand_differentiableAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (fun t => mellin V (-t) * gammaMultiplier t) s := by
  exact ((compact_source_mellin_differentiable V a b ha hsupp hV (-s)).comp s
    differentiableAt_id.neg).mul (gammaMultiplier_differentiableAt s hs)

end CubicReflectionKernel

open scoped BigOperators Classical

namespace DescentWeightedCauchy

theorem weighted_cauchy_sq {ι : Type*} (s : Finset ι)
    (w U V : ι → ℂ) :
    ‖∑ i ∈ s, w i * U i * star (V i)‖ ^ 2 ≤
      (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2) := by
  have hnorm : ‖∑ i ∈ s, w i * U i * star (V i)‖ ≤
      ∑ i ∈ s, ‖w i‖ * ‖U i‖ * ‖V i‖ := by
    simpa only [norm_mul, norm_star] using
      norm_sum_le s (fun i => w i * U i * star (V i))
  calc
    _ ≤ (∑ i ∈ s, ‖w i‖ * ‖U i‖ * ‖V i‖) ^ 2 :=
      sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ => by positivity)) |>.mpr hnorm
    _ ≤ _ := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (fun i _ => by positivity) (fun i _ => by positivity)
      (fun i _ => by ring_nf; exact le_rfl)

theorem weighted_cauchy {ι : Type*} (s : Finset ι)
    (w U V : ι → ℂ) :
    ‖∑ i ∈ s, w i * U i * star (V i)‖ ≤
      Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2) := by
  have h1 : 0 ≤ ∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have h2 : 0 ≤ ∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have hs := weighted_cauchy_sq s w U V
  have he1 := Real.sq_sqrt h1
  have he2 := Real.sq_sqrt h2
  have hp : (Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2)) ^ 2 =
      (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2) := by rw [mul_pow, he1, he2]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (hp ▸ hs)

theorem weighted_energy_pushforward {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (f : ι → κ) (w : ι → ℂ)
    (P : κ → ℂ) (B : κ → ℝ)
    (hmap : ∀ i ∈ s, f i ∈ t)
    (hfib : ∀ y ∈ t, (∑ i ∈ s with f i = y, ‖w i‖) ≤ B y) :
    (∑ i ∈ s, ‖w i‖ * ‖P (f i)‖ ^ 2) ≤
      ∑ y ∈ t, B y * ‖P y‖ ^ 2 := by
  calc
    _ = ∑ y ∈ t, ∑ i ∈ s with f i = y, ‖w i‖ * ‖P (f i)‖ ^ 2 := by
      symm
      exact Finset.sum_fiberwise_of_maps_to hmap _
    _ = ∑ y ∈ t, (∑ i ∈ s with f i = y, ‖w i‖) * ‖P y‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ ≤ _ := Finset.sum_le_sum (fun y hy =>
      mul_le_mul_of_nonneg_right (hfib y hy) (sq_nonneg _))

theorem bounded_energy_pushforward {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (f : ι → κ) (w : ι → ℂ)
    (P : κ → ℂ) (C : ℝ)
    (hmap : ∀ i ∈ s, f i ∈ t) (hw : ∀ i ∈ s, ‖w i‖ ≤ C) :
    (∑ i ∈ s, ‖w i‖ * ‖P (f i)‖ ^ 2) ≤
      ∑ y ∈ t, C * (s.filter (fun i => f i = y)).card * ‖P y‖ ^ 2 := by
  apply weighted_energy_pushforward s t f w P _ hmap
  intro y hy
  calc
    _ ≤ ∑ i ∈ s with f i = y, C := Finset.sum_le_sum
      (fun i hi => hw i (Finset.mem_filter.mp hi).1)
    _ = _ := by simp [mul_comm]

abbrev O := ActualEisensteinCubic.O

def firstRowMap (E : Ideal O) (x : Ideal O × Ideal O) : Ideal O :=
  x.2 * x.1 ^ 2 * E

theorem firstRowMap_fst_dvd (E : Ideal O) (x : Ideal O × Ideal O) :
    x.1 ∣ firstRowMap E x := by
  refine ⟨x.2 * x.1 * E, ?_⟩
  simp only [firstRowMap]
  ring

theorem firstRowMap_fst_injective_on_fiber
    (s : Finset (Ideal O × Ideal O)) (E Y : Ideal O) (hY : Y ≠ ⊥) :
    Set.InjOn (Prod.fst : Ideal O × Ideal O → Ideal O)
      {x | x ∈ s ∧ firstRowMap E x = Y} := by
  intro x hx z hz hfst
  have hx' := hx.2
  have hz' := hz.2
  have hfac : x.1 ^ 2 * E ≠ 0 := by
    intro he
    apply hY
    rw [← hx']
    simp [firstRowMap, mul_assoc, he]
  apply Prod.ext hfst
  apply mul_right_cancel₀ hfac
  calc
    x.2 * (x.1 ^ 2 * E) = Y := by simpa [firstRowMap, mul_assoc] using hx'
    _ = z.2 * (x.1 ^ 2 * E) := by simpa [firstRowMap, mul_assoc, hfst] using hz'.symm

theorem firstRowMap_fiber_card_le
    (s : Finset (Ideal O × Ideal O)) (E Y : Ideal O) (hY : Y ≠ ⊥) :
    (s.filter (fun x => firstRowMap E x = Y)).card ≤
      (IdealMobiusDivisorSum.idealDivisors Y).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro x hx
    change x.1 ∈ IdealMobiusDivisorSum.idealDivisors Y
    rw [IdealMobiusDivisorSum.mem_idealDivisors hY]
    rw [← (Finset.mem_filter.mp hx).2]
    exact firstRowMap_fst_dvd E x
  · intro x hx z hz he
    exact firstRowMap_fst_injective_on_fiber s E Y hY
      (Finset.mem_filter.mp hx) (Finset.mem_filter.mp hz) he

theorem first_energy_pushforward
    (s : Finset (Ideal O × Ideal O)) (t : Finset (Ideal O))
    (E : Ideal O) (w : Ideal O × Ideal O → ℂ) (P : Ideal O → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hmap : ∀ x ∈ s, firstRowMap E x ∈ t)
    (ht : ∀ Y ∈ t, Y ≠ ⊥) (hw : ∀ x ∈ s, ‖w x‖ ≤ C) :
    (∑ x ∈ s, ‖w x‖ * ‖P (firstRowMap E x)‖ ^ 2) ≤
      ∑ Y ∈ t, C * (IdealMobiusDivisorSum.idealDivisors Y).card * ‖P Y‖ ^ 2 := by
  apply (bounded_energy_pushforward s t (firstRowMap E) w P C hmap hw).trans
  apply Finset.sum_le_sum
  intro Y hY
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast firstRowMap_fiber_card_le s E Y (ht Y hY)) hC)
    (sq_nonneg _)

def firstElementRowMap (e : O) (x : Ideal O × O) : O :=
  x.2 * ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e

theorem firstElementRowMap_label_dvd (e : O) (x : Ideal O × O) :
    x.1 ∣ Ideal.span {firstElementRowMap e x} := by
  rw [← ConcretePrimeRowBridge.span_idealGenerator x.1]
  apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr
  refine ⟨x.2 * ConcretePrimeRowBridge.idealGenerator x.1 * e, ?_⟩
  simp only [firstElementRowMap]
  ring

theorem firstElementRowMap_fiber_card_le
    (s : Finset (Ideal O × O)) (e y : O) (hy : y ≠ 0) :
    (s.filter (fun x => firstElementRowMap e x = y)).card ≤
      (IdealMobiusDivisorSum.idealDivisors (Ideal.span {y})).card := by
  have hyI : (Ideal.span {y} : Ideal O) ≠ ⊥ := by
    intro h
    have hm : y ∈ (Ideal.span {y} : Ideal O) := Ideal.subset_span (by first | simp | exact_mod_cast le_top)
    rw [h] at hm
    exact hy hm
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro x hx
    change x.1 ∈ IdealMobiusDivisorSum.idealDivisors (Ideal.span {y})
    rw [IdealMobiusDivisorSum.mem_idealDivisors hyI,
      ← (Finset.mem_filter.mp hx).2]
    exact firstElementRowMap_label_dvd e x
  · intro x hx z hz hfst
    have hx' := (Finset.mem_filter.mp hx).2
    have hz' := (Finset.mem_filter.mp hz).2
    have hfac : ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e ≠ 0 := by
      intro he
      apply hy
      rw [← hx']
      simp [firstElementRowMap, mul_assoc, he]
    apply Prod.ext hfst
    apply mul_right_cancel₀ hfac
    calc
      x.2 * (ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e) = y := by
        simpa [firstElementRowMap, mul_assoc] using hx'
      _ = z.2 * (ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e) := by
        simpa [firstElementRowMap, mul_assoc, hfst] using hz'.symm

theorem first_element_energy_pushforward
    (s : Finset (Ideal O × O)) (t : Finset O)
    (e : O) (w : Ideal O × O → ℂ) (P : O → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hmap : ∀ x ∈ s, firstElementRowMap e x ∈ t)
    (ht : ∀ y ∈ t, y ≠ 0) (hw : ∀ x ∈ s, ‖w x‖ ≤ C) :
    (∑ x ∈ s, ‖w x‖ * ‖P (firstElementRowMap e x)‖ ^ 2) ≤
      ∑ y ∈ t, C * (IdealMobiusDivisorSum.idealDivisors (Ideal.span {y})).card *
        ‖P y‖ ^ 2 := by
  apply (bounded_energy_pushforward s t (firstElementRowMap e) w P C hmap hw).trans
  apply Finset.sum_le_sum
  intro y hyt
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (by exact_mod_cast firstElementRowMap_fiber_card_le s e y (ht y hyt)) hC)
    (sq_nonneg _)

end DescentWeightedCauchy

end

end OAI

end


