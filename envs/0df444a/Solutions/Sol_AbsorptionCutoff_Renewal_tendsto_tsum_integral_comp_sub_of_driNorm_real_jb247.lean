-- Prove2me | solution 1 for AbsorptionCutoff.Renewal.tendsto_tsum_integral_comp_sub_of_driNorm_real_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:44:15.814108+00:00
-- url     : https://prove2.me/submissions/333eaad4-5b42-4317-8d6d-003b863e4521

import Mathlib
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Restrict
import Definitions.Def_OAIQ247J000

section
-- module Solutions.OAIQ247_JB.Supercritical_Renewal
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# A renewal mini-library

Paper §7 concludes `lem:nd-gaussian-renewal` with the *key renewal theorem for
directly Riemann integrable functions on the whole line* (Feller, *An Introduction
to Probability Theory and its Applications* vol. 2, §XI.9 (9.2) and §XI.1
(1.10)--(1.17); Gut, *Stopped Random Walks*, Thm. 6.6 and Rem. 6.4).

Mathlib v4.32.0 contains **no renewal theory at all** — the identifiers
`renewal`, `Blackwell`, `directly Riemann`, `ladder` and `random walk` do not
occur anywhere in the library. It does, however, provide the convolution of
measures `MeasureTheory.Measure.conv` (notation `∗`, the pushforward of
`μ.prod ν` under `+`) together with associativity, commutativity, the `dirac 0`
unit laws, `SFinite`/`IsProbabilityMeasure` instances and the integral formulas
`MeasureTheory.integral_conv` / `Measure.lintegral_conv`. That is the substrate
this file is built on.

This module is deliberately a **leaf**: it depends only on Mathlib, never on the
rest of `AbsorptionCutoff`. The chapter-specific bridge — instantiating everything here
at the Cramér-tilted increment law `μ̂_{A,N}` — lives in
`AbsorptionCutoff.Supercritical.StationaryEquation`.

## Main definitions

* `Renewal.convPow`: the convolution power `μ^{*n}`, the law of the random walk
  step `S_n = Z_1 + ⋯ + Z_n`.
* `Renewal.renewalMeasure`: the renewal measure `U = ∑_{n ≥ 0} μ^{*n}`.
* `Renewal.abelRenewalMeasure`: the Abel-discounted renewal measure
  `U_r = ∑_{n ≥ 0} rⁿ μ^{*n}`, the regularization used to identify Blackwell's
  constant `1/m̂`.
* `Renewal.expTransform`: the `ℝ≥0∞`-valued exponential transform
  `∫ e^{-θz} dμ`, which turns convolution into multiplication.

## Main results

* `Renewal.renewalMeasure_le_of_expTransform`: the explicit geometric left-tail
  bound `U(s) ≤ e^{θb}/(1 - ∫ e^{-θz}dμ)` for `s ⊆ (-∞, b]`, from which
* `Renewal.renewalMeasure_lt_top_of_expTransform_lt_one` and
  `Renewal.renewalMeasure_Icc_lt_top`: local finiteness of `U`.
* `Renewal.driNorm`: the directly-Riemann-integrable norm
  `∑_{k∈ℤ} sup_{[k,k+1]} g`, and `Renewal.tsum_lintegral_comp_sub_le`: a uniform
  bound `C` on the `U`-mass of unit cells gives `∑ₙ∫g(y−s)dμ^{*n} ≤ C‖g‖_DRI`.
* `Renewal.lintegral_le_driNorm`: `‖·‖_{L¹} ≤ ‖·‖_DRI`, whence
  `Renewal.integrable_of_driNorm` and `Renewal.norm_integral_sub_le_driNorm`.
* `Renewal.exists_hasCompactSupport_driNorm_sub_lt`: a continuous kernel of
  finite d.R.i. norm is `‖·‖_DRI`-approximable by continuous compactly supported
  ones.
* `Renewal.summable_integral_comp_sub_of_driNorm` and
  `Renewal.norm_tsum_integral_comp_sub_sub_le`: the smoothed renewal series of a
  kernel with finite d.R.i. norm converges absolutely, and two kernels' series
  differ by at most `C‖z−w‖_DRI` uniformly in `y`.

## Development plan

1. the convolution power `μ^{*n}` and the renewal measure `U` (this file);
2. Blackwell's renewal theorem;
3. the key renewal theorem for directly Riemann integrable functions on the line;
4. the paper's abstract measure-valued form
   (`eq:nd-abstract-renewal-equation` → `eq:nd-abstract-renewal-limit`).

The smoothing kernel (`unitBox`, `triangle`, `sincSq` and their Fourier
identities) lives in the sibling leaf module
`AbsorptionCutoff.Supercritical.RenewalKernel`, split off purely for build time.
-/

open MeasureTheory
open scoped ENNReal NNReal FourierTransform

namespace AbsorptionCutoff

namespace Renewal

variable {M : Type*} [AddMonoid M] [MeasurableSpace M]

lemma convPow_succ (μ : Measure M) (n : ℕ) : convPow μ (n + 1) = convPow μ n ∗ μ := rfl

instance instSFiniteConvPow (μ : Measure M) [SFinite μ] (n : ℕ) : SFinite (convPow μ n) := by
  induction n with
  | zero => rw [convPow_zero]; infer_instance
  | succ n ih => rw [convPow_succ]; exact Measure.sfinite_conv_of_sfinite _ _

instance instIsProbabilityMeasureConvPow [MeasurableAdd₂ M] (μ : Measure M)
    [IsProbabilityMeasure μ] (n : ℕ) : IsProbabilityMeasure (convPow μ n) := by
  induction n with
  | zero => rw [convPow_zero]; infer_instance
  | succ n ih => rw [convPow_succ]; exact Measure.probabilitymeasure_of_probabilitymeasures_conv _ _

@[simp]
lemma convPow_one [MeasurableAdd₂ M] (μ : Measure M) [SFinite μ] : convPow μ 1 = μ := by
  rw [convPow_succ, convPow_zero, Measure.dirac_zero_conv]

lemma renewalMeasure_apply (μ : Measure M) {s : Set M} (hs : MeasurableSet s) :
    renewalMeasure μ s = ∑' n, convPow μ n s := Measure.sum_apply _ hs

/-- Integration against `U` *is* the smoothed renewal series, with no side
conditions, because `U` is a `Measure.sum` and the `ℝ≥0∞`-valued integral commutes
with countable sums of measures unconditionally. This is the identity that lets a
bound on the renewal *measure* of cells control the whole series at once. -/
lemma lintegral_renewalMeasure (μ : Measure M) (f : M → ℝ≥0∞) :
    ∫⁻ x, f x ∂(renewalMeasure μ) = ∑' n, ∫⁻ x, f x ∂(convPow μ n) :=
  lintegral_sum_measure _ _

/-!
### The Abel-discounted renewal measure

Identifying Blackwell's constant `1/m̂` is done by *Abel regularization*: the
undiscounted resolvent `(1 - χ(-2πt))⁻¹` has a genuine pole at the origin, and a
symmetric principal-value treatment of it sees only half the boundary mass,
producing `1/(2m̂)`. Discounting by `rⁿ` for `0 < r < 1` moves the pole off the
real axis — `1 - rχ(-2πt)` is bounded away from zero — and the model denominator
`(1-r) + 2π i r m̂ t` has a *one-sided* exponential inverse transform, which is
what supplies the missing half. The limits are then taken in the order `r ↑ 1` at
fixed `y`, and only afterwards `y → ∞`; see `A4G4_BLACKWELL_PROOF_NOTE.tex` §3.

The discounted measure is scaled in `ℝ≥0∞`, so it stays a genuine (nonnegative)
measure and `abelRenewalMeasure_mono` holds. That monotonicity in `r` is not
cosmetic: it is what licenses monotone convergence from the discounted series
back to the actual renewal series at `r = 1`.
-/

/-!
### Local finiteness of the renewal measure

For a general random walk drifting to `+∞`, local finiteness of `U` is proved by
a ladder-height decomposition. Here we do not need that generality: the increment
law the chapter supplies is the *Cramér tilt* `μ̂_{A,N}`, and the tilt comes with
a whole interval of finite exponential moments. Concretely, for
`0 < θ < β_{A,N}`,

  `∫ e^{-θ z} μ̂_{A,N}(dz) = ℳ_{A,N}(β_{A,N} - θ) < 1`,

the strict inequality being `gaussianTransferMoment_lt_one_of_lt_cramerExponent`
in `AbsorptionCutoff.Supercritical.StationaryEquation`. A Chernoff bound then makes the
convolution powers decay *geometrically* on every half-line `(-∞, b]`, so `U` is
finite there — much stronger than local finiteness, and enough for everything
downstream.

The transform is taken with values in `ℝ≥0∞` so that no integrability side
conditions are needed; the real-valued identification against `ℳ_{A,N}` is done
where the transform is applied.
-/

lemma expTransform_def (θ : ℝ) (μ : Measure ℝ) :
    expTransform θ μ = ∫⁻ z, ENNReal.ofReal (Real.exp (-(θ * z))) ∂μ := rfl

@[simp]
lemma expTransform_dirac_zero (θ : ℝ) : expTransform θ (Measure.dirac 0) = 1 := by
  rw [expTransform_def, lintegral_dirac' _ (by fun_prop)]
  simp

/-- The exponential transform turns convolution into multiplication. -/
lemma expTransform_conv (θ : ℝ) (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    expTransform θ (ν ∗ μ) = expTransform θ ν * expTransform θ μ := by
  rw [expTransform_def, Measure.lintegral_conv (by fun_prop)]
  have key : ∀ x y : ℝ, ENNReal.ofReal (Real.exp (-(θ * (x + y))))
      = ENNReal.ofReal (Real.exp (-(θ * x))) * ENNReal.ofReal (Real.exp (-(θ * y))) := by
    intro x y
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    ring_nf
  have inner : ∀ x : ℝ, ∫⁻ y, ENNReal.ofReal (Real.exp (-(θ * (x + y)))) ∂μ
      = ENNReal.ofReal (Real.exp (-(θ * x))) * expTransform θ μ := by
    intro x
    simp_rw [key x]
    exact lintegral_const_mul _ (by fun_prop)
  simp_rw [inner]
  exact lintegral_mul_const _ (by fun_prop)

/-- `𝔼 e^{-θ S_n} = (𝔼 e^{-θ Z})^n`. -/
lemma expTransform_convPow (θ : ℝ) (μ : Measure ℝ) [SFinite μ] (n : ℕ) :
    expTransform θ (convPow μ n) = expTransform θ μ ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [convPow_succ, expTransform_conv, ih, pow_succ]

/-- Chernoff bound: a set contained in the half-line `(-∞, b]` has measure at
most `e^{θb}` times the exponential transform. -/
lemma measure_le_expTransform {θ b : ℝ} (hθ : 0 < θ) (ν : Measure ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) (hsb : s ⊆ Set.Iic b) :
    ν s ≤ ENNReal.ofReal (Real.exp (θ * b)) * expTransform θ ν := by
  calc ν s = ∫⁻ _x in s, 1 ∂ν := by simp
    _ ≤ ∫⁻ x in s, ENNReal.ofReal (Real.exp (θ * b))
          * ENNReal.ofReal (Real.exp (-(θ * x))) ∂ν := by
        refine lintegral_mono_ae ((ae_restrict_iff' hs).2 (.of_forall fun x hx => ?_))
        have hxb : x ≤ b := hsb hx
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by nlinarith))
    _ ≤ ENNReal.ofReal (Real.exp (θ * b)) * expTransform θ ν := by
        rw [lintegral_const_mul _ (by fun_prop)]
        exact mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

/-- **The explicit geometric left-tail bound on the renewal measure.**

If the increment law has exponential transform `λ := ∫ e^{-θz} dμ < 1` at some
`θ > 0`, then on every set contained in a half-line `(-∞, b]`,

  `U(s) ≤ e^{θb} / (1 - λ)`,

with the constant depending on `s` only through `b`. This is the *quantitative*
form of `renewalMeasure_lt_top_of_expTransform_lt_one`; the two-sided uniform
cell bound needs the constant, not just finiteness, because the right-hand tail
bound it is paired with is itself uniform.

No hypothesis on `λ` is needed for the inequality itself — at `λ ≥ 1` the right-hand
side is `∞` — so it is stated unconditionally; `λ < 1` is what makes it useful. -/
theorem renewalMeasure_le_of_expTransform {μ : Measure ℝ} [SFinite μ] {θ : ℝ}
    (hθ : 0 < θ) {s : Set ℝ} (hs : MeasurableSet s) {b : ℝ}
    (hsb : s ⊆ Set.Iic b) :
    renewalMeasure μ s ≤ ENNReal.ofReal (Real.exp (θ * b)) * (1 - expTransform θ μ)⁻¹ := by
  have hbound : ∀ n : ℕ, convPow μ n s
      ≤ ENNReal.ofReal (Real.exp (θ * b)) * expTransform θ μ ^ n := fun n => by
    calc convPow μ n s ≤ ENNReal.ofReal (Real.exp (θ * b)) * expTransform θ (convPow μ n) :=
          measure_le_expTransform hθ _ hs hsb
      _ = ENNReal.ofReal (Real.exp (θ * b)) * expTransform θ μ ^ n := by rw [expTransform_convPow]
  rw [renewalMeasure_apply _ hs]
  refine le_trans (ENNReal.tsum_le_tsum hbound) ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- **The renewal measure of a set is dominated by any kernel bounded below on it.**

If `v(y − ·) ≥ c > 0` on `I`, then `U(I) ≤ (∑ₙ ∫v(y−z)dμ^{*n})/c`.

This is the bridge from the *smoothed* renewal series — which the Abel argument
evaluates — back to the renewal measure of an actual interval, and hence the first
half of the uniform local bound. The comparison is done for each convolution power
separately: `c·μ^{*n}(I) ≤ ∫_I v(y−z)dμ^{*n} ≤ ∫ v(y−z)dμ^{*n}`, the second step
using `v ≥ 0`. Summing needs `ENNReal.ofReal_tsum_of_nonneg` to move the whole
real series into `ℝ≥0∞` at once, since the individual measures are `ℝ≥0∞`-valued
while the integrals are real. -/
theorem renewalMeasure_le_ofReal_tsum_integral {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {v : ℝ → ℝ} (hv0 : ∀ x, 0 ≤ v x) (hvc : Continuous v) {B : ℝ} (hB : ∀ x, v x ≤ B)
    {I : Set ℝ} (hI : MeasurableSet I) {y c : ℝ} (hc : 0 < c)
    (hvI : ∀ z ∈ I, c ≤ v (y - z))
    (hsum : Summable fun n => ∫ z, v (y - z) ∂(convPow μ n)) :
    renewalMeasure μ I ≤ ENNReal.ofReal ((∑' n, ∫ z, v (y - z) ∂(convPow μ n)) / c) := by
  have hterm : ∀ n : ℕ, (convPow μ n) I
      ≤ ENNReal.ofReal ((∫ z, v (y - z) ∂(convPow μ n)) / c) := by
    intro n
    have hint : Integrable (fun z : ℝ => v (y - z)) (convPow μ n) := by
      refine (integrable_const B).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
      · exact (hvc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      · rw [Real.norm_of_nonneg (hv0 _)]
        exact hB _
    have h1 : ∫ z in I, c ∂(convPow μ n) ≤ ∫ z in I, v (y - z) ∂(convPow μ n) :=
      setIntegral_mono_on (integrable_const c).integrableOn hint.integrableOn hI hvI
    have h2 : ∫ z in I, v (y - z) ∂(convPow μ n) ≤ ∫ z, v (y - z) ∂(convPow μ n) :=
      setIntegral_le_integral hint (Filter.Eventually.of_forall fun z => hv0 _)
    rw [setIntegral_const, smul_eq_mul] at h1
    have hle : ((convPow μ n) I).toReal ≤ (∫ z, v (y - z) ∂(convPow μ n)) / c := by
      rw [le_div_iff₀ hc]
      calc ((convPow μ n) I).toReal * c = c * ((convPow μ n) I).toReal := by ring
        _ ≤ ∫ z, v (y - z) ∂(convPow μ n) := by
            rw [Measure.real] at h1
            linarith
    calc (convPow μ n) I = ENNReal.ofReal ((convPow μ n) I).toReal :=
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal ((∫ z, v (y - z) ∂(convPow μ n)) / c) := ENNReal.ofReal_le_ofReal hle
  have hnn : ∀ n : ℕ, 0 ≤ (∫ z, v (y - z) ∂(convPow μ n)) / c :=
    fun n => div_nonneg (integral_nonneg fun z => hv0 _) hc.le
  calc renewalMeasure μ I = ∑' n, (convPow μ n) I := renewalMeasure_apply _ hI
    _ ≤ ∑' n, ENNReal.ofReal ((∫ z, v (y - z) ∂(convPow μ n)) / c) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal ((∑' n, ∫ z, v (y - z) ∂(convPow μ n)) / c) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg hnn (hsum.div_const c), tsum_div_const]

/-!
### Nonlatticeness and the characteristic function

The chosen proof route for Blackwell's theorem is Fourier inversion against
smoothing kernels with compactly supported Fourier transform (see
`A4G4_BLACKWELL_PROOF_NOTE.tex`). Nonlatticeness enters that argument
at exactly one point, and in exactly one form: the characteristic function
`χ(t) = ∫ e^{itz} dμ` must avoid the value `1` off the origin, so that
`1 - χ` is bounded away from `0` on the compact set where the transform of the
smoothing kernel lives.
-/

/-- **A nonlattice probability measure has `charFun μ t ≠ 1` for every `t ≠ 0`.**

If `χ(t) = 1` then, taking real parts, `∫ (1 - cos (t z)) dμ = 0`; the integrand
is nonnegative, so `cos (t z) = 1` for `μ`-a.e. `z`, i.e. `μ` is carried by the
lattice `(2π/t) ℤ`, contradicting `Nonlattice`. -/
theorem charFun_ne_one_of_nonlattice {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) {t : ℝ} (ht : t ≠ 0) : charFun μ t ≠ 1 := by
  intro h
  have hint : Integrable (fun x : ℝ => Complex.exp (t * x * Complex.I)) μ := by
    refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun x => ?_)
    have : ((t : ℂ) * x * Complex.I) = ((t * x : ℝ) : ℂ) * Complex.I := by push_cast <;> ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have hcos : Integrable (fun x : ℝ => Real.cos (t * x)) μ := by
    refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun x => ?_)
    simpa using Real.abs_cos_le_one (t * x)
  -- The real part of the defining integral of `charFun`.
  have hre : ∫ x, Real.cos (t * x) ∂μ = 1 := by
    have h1 : ∫ x, ((Complex.exp ((t : ℂ) * x * Complex.I)).re) ∂μ = (charFun μ t).re := by
      rw [charFun_apply_real, ← Complex.reCLM_apply,
        ← ContinuousLinearMap.integral_comp_comm _ hint]
      rfl
    have h2 : ∀ x : ℝ, (Complex.exp ((t : ℂ) * x * Complex.I)).re = Real.cos (t * x) := by
      intro x
      have : ((t : ℂ) * x * Complex.I) = ((t * x : ℝ) : ℂ) * Complex.I := by push_cast <;> ring
      rw [this, Complex.exp_ofReal_mul_I_re]
    simp only [h2] at h1
    rw [h1, h]
    simp
  have key : ∫ x, (1 - Real.cos (t * x)) ∂μ = 0 := by
    rw [integral_sub (integrable_const 1) hcos, hre]
    simp
  have hae : ∀ᵐ x ∂μ, Real.cos (t * x) = 1 := by
    have hnn : 0 ≤ᵐ[μ] fun x => 1 - Real.cos (t * x) :=
      Filter.Eventually.of_forall fun x => by simpa using Real.cos_le_one (t * x)
    have := (integral_eq_zero_iff_of_nonneg_ae hnn ((integrable_const 1).sub hcos)).mp key
    filter_upwards [this] with x hx
    simp only [Pi.zero_apply] at hx
    linarith
  -- Hence `μ` is carried by the lattice `(2π/t) ℤ`.
  set S : Set ℝ := {x : ℝ | ∃ k : ℤ, x = 0 + k * (2 * Real.pi / t)} with hS
  have hsub : ∀ᵐ x ∂μ, x ∈ S := by
    filter_upwards [hae] with x hx
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (t * x)).mp hx
    exact ⟨n, by field_simp <;> linarith [hn]⟩
  have hcount : S.Countable := by
    have : S = Set.range (fun k : ℤ => (0 : ℝ) + k * (2 * Real.pi / t)) := by
      ext x; simp [hS, eq_comm]
    rw [this]; exact Set.countable_range _
  exact hμ 0 (2 * Real.pi / t)
    ((prob_compl_eq_zero_iff hcount.measurableSet).mp (ae_iff.mp hsub))

/-- **`1 - charFun μ` is bounded away from `0` on a compact annulus.**

The Fourier proof of Blackwell's theorem integrates `(1 - charFun μ t)⁻¹` against
the transform of the smoothing kernel, which is supported in a compact interval
`[-T,T]`; near the origin the integrand is handled by the pole subtraction, and
on the remaining compact annulus `δ ≤ |t| ≤ T` this lemma keeps it bounded.
Nonlatticeness enters only through `charFun_ne_one_of_nonlattice`, and
compactness upgrades the pointwise nonvanishing to a uniform bound. -/
theorem exists_pos_le_norm_one_sub_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    ∃ c > 0, ∀ t : ℝ, |t| ≤ T → δ ≤ |t| → c ≤ ‖1 - charFun μ t‖ := by
  set K : Set ℝ := Set.Icc (-T) T ∩ {t : ℝ | δ ≤ |t|} with hK
  have hKc : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hcont : Continuous fun t : ℝ => ‖1 - charFun μ t‖ :=
    (continuous_const.sub continuous_charFun).norm
  rcases K.eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, fun t htT htδ => ?_⟩
    exact absurd (show t ∈ K from ⟨abs_le.mp htT, htδ⟩) (by rw [hemp]; exact Set.notMem_empty t)
  · obtain ⟨t₀, ht₀K, ht₀min⟩ := hKc.exists_isMinOn hne hcont.continuousOn
    have ht₀ne : t₀ ≠ 0 := by
      intro h
      have h' := ht₀K.2
      simp only [Set.mem_setOf_eq, h, abs_zero] at h'
      linarith
    have hpos : 0 < ‖1 - charFun μ t₀‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      exact fun h => charFun_ne_one_of_nonlattice hμ ht₀ne h.symm
    exact ⟨‖1 - charFun μ t₀‖, hpos,
      fun t htT htδ => ht₀min (show t ∈ K from ⟨abs_le.mp htT, htδ⟩)⟩

/-- **The characteristic function of a convolution power is a power**,
`χ_{μ^{*n}} = χ_μ^n`. This is the Fourier counterpart of `expTransform_convPow`,
and it is what turns the renewal measure `U = ∑ₙ μ^{*n}` into the geometric
series `∑ₙ χ^n = (1 - χ)⁻¹` under the Parseval atom below. -/
lemma charFun_convPow (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) (t : ℝ) :
    charFun (convPow μ n) t = (charFun μ t) ^ n := by
  induction n with
  | zero => simp [convPow_zero, charFun_dirac]
  | succ n ih => rw [convPow_succ, charFun_conv, ih, pow_succ]

/-!
### The pole at the origin

`(1 - charFun μ t)⁻¹` blows up at `t = 0`; that pole is precisely what carries
the `1/m̂` of Blackwell's theorem. The three lemmas below quantify it. They are
the only place where the **deliberate hypothesis strengthening** `MemLp id 2 μ`
(a finite second moment, where sharp Feller needs only a finite mean) is used;
`μ̂_{A,N}` has exponential moments, so it costs nothing at the instantiation.
-/

/-- The second-order Taylor expansion of the characteristic function at the
origin: `χ(t) = 1 + i m t - (∫x²) t²/2 + o(t²)`. Specialised from Mathlib's
`taylor_isLittleO_univ` and `taylorWithinEval_charFun_zero` — note the ready-made
`taylor_charFun_two` is stated only for a *standardised* law (mean `0`, variance
`1`) pushed forward along a random variable, so it is not usable here. -/
theorem charFun_taylor {μ : Measure ℝ} [IsProbabilityMeasure μ] (hint : MemLp id 2 μ) :
    (fun t : ℝ => charFun μ t - (1 + ((∫ x, x ∂μ : ℝ) : ℂ) * t * Complex.I
        - ((∫ x, x ^ 2 ∂μ : ℝ) : ℂ) * t ^ 2 / 2)) =o[nhds 0] fun t : ℝ => t ^ 2 := by
  have h := taylor_isLittleO_univ (f := charFun μ) (x₀ := (0 : ℝ)) (n := 2)
    (contDiff_charFun hint)
  simp only [sub_zero] at h
  refine h.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards with t
  rw [taylorWithinEval_charFun_zero hint t]
  simp [Finset.sum_range_succ]
  linear_combination (↑t ^ 2 * ↑(∫ x : ℝ, x ^ 2 ∂μ) * (1 / 2) : ℂ) * Complex.I_sq

/-- The quantitative form of the expansion: `1 - χ(t) + i m t = O(t²)` near the
origin. -/
theorem exists_norm_one_sub_charFun_add_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : MemLp id 2 μ) :
    ∃ δ > 0, ∃ K ≥ (0 : ℝ), ∀ t : ℝ, |t| ≤ δ →
      ‖1 - charFun μ t + ((∫ x, x ∂μ : ℝ) : ℂ) * t * Complex.I‖ ≤ K * t ^ 2 := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  set c : ℝ := ∫ x, x ^ 2 ∂μ with hcdef
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp ((charFun_taylor hint).def one_pos)
  refine ⟨ε / 2, by linarith, 1 + |c| / 2, by positivity, fun t ht => ?_⟩
  have hd : dist t 0 < ε := by
    rw [Real.dist_eq, sub_zero]; linarith [abs_nonneg t]
  have hsmall : ‖charFun μ t - (1 + (m : ℂ) * t * Complex.I - (c : ℂ) * t ^ 2 / 2)‖
      ≤ 1 * ‖t ^ 2‖ := hball hd
  have hkey : (1 : ℂ) - charFun μ t + (m : ℂ) * t * Complex.I
      = -(charFun μ t - (1 + (m : ℂ) * t * Complex.I - (c : ℂ) * t ^ 2 / 2))
        + (c : ℂ) * t ^ 2 / 2 := by ring
  rw [hkey]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_neg]
  have h1 : ‖charFun μ t - (1 + (m : ℂ) * t * Complex.I - (c : ℂ) * t ^ 2 / 2)‖ ≤ t ^ 2 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using hsmall
  have h2 : ‖(c : ℂ) * (t : ℂ) ^ 2 / 2‖ = |c| / 2 * t ^ 2 := by
    rw [norm_div, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
    rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
    ring
  rw [h2]
  linarith

/-- **The simple zero of `1 - charFun μ` at the origin**: for a law with positive
drift `m`, `‖1 - χ(t)‖ ≥ (m/2)|t|` near `0`. Together with
`exists_pos_le_norm_one_sub_charFun` off the origin this bounds the resolvent on
the whole compact interval where the kernel's transform lives. -/
theorem exists_le_norm_one_sub_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) :
    ∃ δ > 0, ∀ t : ℝ, |t| ≤ δ → (∫ x, x ∂μ) / 2 * |t| ≤ ‖1 - charFun μ t‖ := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  obtain ⟨δ, hδ, K, hK, hbound⟩ := exists_norm_one_sub_charFun_add_le hint
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  refine ⟨min δ (m / (2 * (K + 1))), lt_min hδ (by positivity), fun t ht => ?_⟩
  have ht1 : |t| ≤ δ := le_trans ht (min_le_left _ _)
  have ht2 : |t| ≤ m / (2 * (K + 1)) := le_trans ht (min_le_right _ _)
  have hb := hbound t ht1
  have hmt : ‖(m : ℂ) * (t : ℂ) * Complex.I‖ = m * |t| := by simp [abs_of_pos hm]
  have hB : ‖(m : ℂ) * (t : ℂ) * Complex.I‖
      ≤ ‖(1 : ℂ) - charFun μ t + (m : ℂ) * t * Complex.I‖ + ‖(1 : ℂ) - charFun μ t‖ := by
    calc ‖(m : ℂ) * (t : ℂ) * Complex.I‖
        = ‖((1 : ℂ) - charFun μ t + (m : ℂ) * t * Complex.I) - ((1 : ℂ) - charFun μ t)‖ := by
          congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  rw [hmt] at hB
  have habs : K * t ^ 2 ≤ m / 2 * |t| := by
    have hsq : t ^ 2 = |t| * |t| := by rw [← sq_abs t, sq]
    have hmul := mul_le_mul_of_nonneg_left ht2 hK1.le
    have hval : (K + 1) * (m / (2 * (K + 1))) = m / 2 := by field_simp
    rw [hval] at hmul
    calc K * t ^ 2 ≤ (K + 1) * t ^ 2 := by nlinarith [sq_nonneg t]
      _ = ((K + 1) * |t|) * |t| := by rw [hsq]; ring
      _ ≤ (m / 2) * |t| := mul_le_mul_of_nonneg_right hmul (abs_nonneg t)
  linarith

/-- **A nonlattice probability measure has `‖charFun μ t‖ < 1` for every `t ≠ 0`**
— strictly stronger than `charFun_ne_one_of_nonlattice`, and what the `N → ∞`
passage in Blackwell's proof needs: it is what makes `χ(t)^N → 0` pointwise off
the origin.

`‖χ(t)‖ = 1` forces `χ(t) = e^{iθ}` for `θ = arg χ(t)`; rotating by `e^{-iθ}` and
taking real parts gives `∫(1 - cos(tz - θ))dμ = 0`, so `μ` is carried by the
*coset* `θ/t + (2π/t)ℤ`. This is exactly why `Nonlattice` quantifies over the
shift `a` as well as the span `r`: without the shift, this argument would not
close. -/
theorem norm_charFun_lt_one_of_nonlattice {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) {t : ℝ} (ht : t ≠ 0) : ‖charFun μ t‖ < 1 := by
  rcases lt_or_eq_of_le (norm_charFun_le_one (μ := μ) t) with h | h
  · exact h
  exfalso
  obtain ⟨θ, hchi⟩ : ∃ θ : ℝ, charFun μ t = Complex.exp ((θ : ℂ) * Complex.I) := by
    refine ⟨Complex.arg (charFun μ t), ?_⟩
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (charFun μ t)]
    rw [h]; simp
  have hint : Integrable (fun x : ℝ => Complex.exp (((t * x - θ : ℝ) : ℂ) * Complex.I)) μ := by
    refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun x => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  have hcos : Integrable (fun x : ℝ => Real.cos (t * x - θ)) μ := by
    refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun x => ?_)
    simpa using Real.abs_cos_le_one (t * x - θ)
  have hrot : ∫ x, Complex.exp (((t * x - θ : ℝ) : ℂ) * Complex.I) ∂μ = 1 := by
    have hsplit : ∀ x : ℝ, Complex.exp (((t * x - θ : ℝ) : ℂ) * Complex.I)
        = Complex.exp (-(θ : ℂ) * Complex.I) * Complex.exp (((t : ℂ)) * x * Complex.I) := by
      intro x
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [hsplit]
    rw [integral_const_mul, ← charFun_apply_real, hchi, ← Complex.exp_add]
    norm_num
  have hre : ∫ x, Real.cos (t * x - θ) ∂μ = 1 := by
    have h1 : ∫ x, ((Complex.exp (((t * x - θ : ℝ) : ℂ) * Complex.I)).re) ∂μ
        = (∫ x, Complex.exp (((t * x - θ : ℝ) : ℂ) * Complex.I) ∂μ).re := by
      rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ hint]
      rfl
    simp only [Complex.exp_ofReal_mul_I_re] at h1
    rw [h1, hrot]
    simp
  have key : ∫ x, (1 - Real.cos (t * x - θ)) ∂μ = 0 := by
    rw [integral_sub (integrable_const 1) hcos, hre]
    simp
  have hae : ∀ᵐ x ∂μ, Real.cos (t * x - θ) = 1 := by
    have hnn : 0 ≤ᵐ[μ] fun x => 1 - Real.cos (t * x - θ) :=
      Filter.Eventually.of_forall fun x => by simpa using Real.cos_le_one (t * x - θ)
    have h2 := (integral_eq_zero_iff_of_nonneg_ae hnn ((integrable_const 1).sub hcos)).mp key
    filter_upwards [h2] with x hx
    simp only [Pi.zero_apply] at hx
    linarith
  have hcount : {x : ℝ | ∃ k : ℤ, x = θ / t + k * (2 * Real.pi / t)}.Countable := by
    have hrange : {x : ℝ | ∃ k : ℤ, x = θ / t + k * (2 * Real.pi / t)}
        = Set.range (fun k : ℤ => θ / t + k * (2 * Real.pi / t)) := by
      ext x; simp [eq_comm]
    rw [hrange]; exact Set.countable_range _
  have hsub : ∀ᵐ x ∂μ, x ∈ {x : ℝ | ∃ k : ℤ, x = θ / t + k * (2 * Real.pi / t)} := by
    filter_upwards [hae] with x hx
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (t * x - θ)).mp hx
    exact ⟨n, by field_simp <;> linarith [hn]⟩
  exact hμ (θ / t) (2 * Real.pi / t)
    ((prob_compl_eq_zero_iff hcount.measurableSet).mp (ae_iff.mp hsub))

/-- **The resolvent is uniformly controlled by the kernel's transform.**

If `𝓕 w` vanishes off `[-T,T]` and satisfies `‖𝓕w(t)‖ ≤ L|t|` — the two
properties a *difference* kernel with `∫w = 0` has — then

`‖𝓕w(t)‖ ≤ C ‖1 - charFun μ (-2πt)‖`  for every `t`.

This is the inequality that makes the geometric series `∑ₙ χ^n = (1 - χ)⁻¹`
integrable against `𝓕 w` despite the pole: the first-order vanishing of `𝓕 w` at
the origin exactly cancels the simple zero of `1 - χ`. Three regimes: the simple
zero near `0` (`exists_le_norm_one_sub_charFun`), the compact annulus
(`exists_pos_le_norm_one_sub_charFun`), and `𝓕 w = 0` beyond `T`. -/
theorem exists_norm_fourier_le_norm_one_sub_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) {w : ℝ → ℂ} {T L : ℝ}
    (hL0 : 0 ≤ L) (hT : ∀ t : ℝ, T < |t| → 𝓕 w t = 0) (hL : ∀ t : ℝ, ‖𝓕 w t‖ ≤ L * |t|) :
    ∃ C ≥ (0 : ℝ), ∀ t : ℝ, ‖𝓕 w t‖ ≤ C * ‖1 - charFun μ (-(2 * Real.pi * t))‖ := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  obtain ⟨δ, hδ, hnear⟩ := exists_le_norm_one_sub_charFun hint hm
  obtain ⟨c, hc, hann⟩ := exists_pos_le_norm_one_sub_charFun hμ hδ (2 * Real.pi * T)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  refine ⟨max (2 * L / (Real.pi * m)) (L * T / c), le_max_of_le_left (by positivity), fun t => ?_⟩
  have habs : |(-(2 * Real.pi * t))| = 2 * Real.pi * |t| := by
    rw [abs_neg, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hπ]
  rcases le_or_gt (2 * Real.pi * |t|) δ with hsmall | hbig
  · -- near the origin: the simple zero of `1 - χ` absorbs `‖𝓕w(t)‖ ≤ L|t|`
    have h1 : m / 2 * (2 * Real.pi * |t|) ≤ ‖1 - charFun μ (-(2 * Real.pi * t))‖ := by
      have h := hnear (-(2 * Real.pi * t)) (by rw [habs]; exact hsmall)
      rwa [habs] at h
    have hval : (2 * L / (Real.pi * m)) * (m / 2 * (2 * Real.pi * |t|)) = 2 * L * |t| := by
      field_simp
    calc ‖𝓕 w t‖ ≤ L * |t| := hL t
      _ ≤ (2 * L / (Real.pi * m)) * (m / 2 * (2 * Real.pi * |t|)) := by
          rw [hval]; nlinarith [abs_nonneg t]
      _ ≤ max (2 * L / (Real.pi * m)) (L * T / c) * (m / 2 * (2 * Real.pi * |t|)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max (2 * L / (Real.pi * m)) (L * T / c)
            * ‖1 - charFun μ (-(2 * Real.pi * t))‖ :=
          mul_le_mul_of_nonneg_left h1 (le_max_of_le_left (by positivity))
  · rcases le_or_gt |t| T with hin | hout
    · -- the compact annulus, where `1 - χ` is bounded below
      have h1 : c ≤ ‖1 - charFun μ (-(2 * Real.pi * t))‖ := by
        refine hann (-(2 * Real.pi * t)) ?_ ?_
        · rw [habs]; exact mul_le_mul_of_nonneg_left hin (by positivity)
        · rw [habs]; exact hbig.le
      calc ‖𝓕 w t‖ ≤ L * T := le_trans (hL t) (mul_le_mul_of_nonneg_left hin hL0)
        _ = (L * T / c) * c := by field_simp
        _ ≤ max (2 * L / (Real.pi * m)) (L * T / c) * c :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hc.le
        _ ≤ max (2 * L / (Real.pi * m)) (L * T / c)
              * ‖1 - charFun μ (-(2 * Real.pi * t))‖ :=
            mul_le_mul_of_nonneg_left h1 (le_max_of_le_left (by positivity))
    · -- beyond the support of `𝓕 w`
      rw [hT t hout, norm_zero]
      positivity

/-!
### The Parseval atom

The workhorse of the Fourier route: convolving a measure with a test function
whose Fourier transform is integrable turns the measure into its characteristic
function. Applied to `ν = μ^{*n}` and summed over `n` — where `charFun_conv`
makes `charFun (μ^{*n}) = (charFun μ)^n` — this is what converts the renewal
measure into the resolvent `(1 - χ)⁻¹` whose pole at the origin carries the
`1/m̂` of Blackwell's theorem.

Mathlib's Fourier convention carries the `2π` in the exponent
(`𝓕 w t = ∫ e^{-2πi t x} w x dx`), while `charFun` does not
(`charFun ν s = ∫ e^{isz} dν`), whence the argument `-(2π t)` below. Both
conventions are kept as they are: `𝓕` is what the inversion theorem and the
Riemann–Lebesgue lemma are stated for, and `charFun` is what `charFun_conv`
is stated for.
-/

/-- **Parseval / inversion for a probability measure against a test function.**

For a test function `w` that is continuous and integrable with integrable Fourier
transform,
`∫ w(y - z) dν(z) = ∫ 𝓕w(t) e^{2πity} χ_ν(-2πt) dt`,
where `χ_ν = charFun ν`. Fourier inversion inside the `ν`-integral, then Fubini
(legitimate because `‖e^{iθ}‖ = 1` and `ν` is finite, so the joint integrand is
dominated by `‖𝓕w(t)‖`). -/
theorem integral_comp_sub_eq_integral_charFun {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {w : ℝ → ℂ} (hwc : Continuous w) (hw : Integrable w) (hFw : Integrable (𝓕 w)) (y : ℝ) :
    ∫ z, w (y - z) ∂ν
      = ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * charFun ν (-(2 * Real.pi * t)) := by
  have hinv : ∀ x : ℝ,
      w x = ∫ t : ℝ, Complex.exp ((2 * Real.pi * (t * x) : ℝ) * Complex.I) • 𝓕 w t := by
    intro x
    conv_lhs => rw [← congrFun (hwc.fourierInv_fourier_eq hw hFw) x]
    rw [Real.fourierInv_eq']
    simp only [Real.inner_apply]
  have hprod : Integrable (Function.uncurry
      (fun (z : ℝ) (t : ℝ) =>
        Complex.exp ((2 * Real.pi * (t * (y - z)) : ℝ) * Complex.I) • 𝓕 w t))
      (ν.prod volume) := by
    have hsnd : Integrable (fun p : ℝ × ℝ => 𝓕 w p.2) (ν.prod volume) := hFw.comp_snd ν
    refine (hsnd.norm).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable).mul
        hsnd.aestronglyMeasurable
    · obtain ⟨z, t⟩ := p
      change ‖Complex.exp ((2 * Real.pi * (t * (y - z)) : ℝ) * Complex.I) * 𝓕 w t‖ ≤ ‖𝓕 w t‖
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  calc ∫ z, w (y - z) ∂ν
      = ∫ z, ∫ t : ℝ,
          Complex.exp ((2 * Real.pi * (t * (y - z)) : ℝ) * Complex.I) • 𝓕 w t ∂volume ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => hinv (y - z))
    _ = ∫ t : ℝ, ∫ z, Complex.exp ((2 * Real.pi * (t * (y - z)) : ℝ) * Complex.I) • 𝓕 w t ∂ν :=
        integral_integral_swap hprod
    _ = ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * charFun ν (-(2 * Real.pi * t)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [charFun_apply_real, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        -- the goal is an un-beta-reduced redex; `rw` cannot see through it
        beta_reduce
        rw [smul_eq_mul, mul_assoc (𝓕 w t), ← Complex.exp_add, mul_comm]
        congr 1
        push_cast
        ring_nf

/-- The Parseval integrand is integrable, uniformly in the power `n`: the
exponential has modulus `1` and `‖charFun‖ ≤ 1`, so `‖𝓕w(t)‖` dominates. -/
lemma integrable_fourier_mul_charFun_pow {μ : Measure ℝ} [IsProbabilityMeasure μ] {w : ℝ → ℂ}
    (hw : Integrable w) (hFw : Integrable (𝓕 w)) (n : ℕ) (y : ℝ) :
    Integrable (fun t : ℝ => 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * (charFun μ (-(2 * Real.pi * t))) ^ n) := by
  have hFwc : Continuous (𝓕 w) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hw
  refine hFw.norm.mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · exact ((hFwc.mul (Complex.continuous_exp.comp (by fun_prop))).mul
      ((continuous_charFun.comp (by fun_prop)).pow n)).aestronglyMeasurable
  · rw [norm_mul, norm_mul, norm_pow]
    have h1 : ‖Complex.exp ((2 : ℂ) * Real.pi * t * y * Complex.I)‖ = 1 := by
      have hcast : ((2 : ℂ) * Real.pi * t * y * Complex.I)
          = ((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I := by push_cast <;> ring
      rw [hcast, Complex.norm_exp_ofReal_mul_I]
    rw [h1, mul_one]
    have h2 : ‖charFun μ (-(2 * Real.pi * t))‖ ^ n ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (norm_charFun_le_one _)
    calc ‖𝓕 w t‖ * ‖charFun μ (-(2 * Real.pi * t))‖ ^ n ≤ ‖𝓕 w t‖ * 1 :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = ‖𝓕 w t‖ := mul_one _

/-- **The truncated Parseval identity.** Summing the atom over the first `N`
convolution powers turns the partial renewal measure into a geometric sum of
characteristic functions:

`∑_{n<N} ∫ w(y−z) μ^{*n}(dz) = ∫ 𝓕w(t) e^{2πity} ∑_{n<N} χ(−2πt)^n dt`.

The sum is finite, so no convergence hypothesis is needed here; the passage to
`N = ∞` is the delicate step (the geometric sum `(1 − χ)⁻¹` has a pole at the
origin), and is handled separately. -/
theorem sum_integral_comp_sub_eq {μ : Measure ℝ} [IsProbabilityMeasure μ] {w : ℝ → ℂ}
    (hwc : Continuous w) (hw : Integrable w) (hFw : Integrable (𝓕 w)) (N : ℕ) (y : ℝ) :
    ∑ n ∈ Finset.range N, ∫ z, w (y - z) ∂(convPow μ n)
      = ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * ∑ n ∈ Finset.range N, (charFun μ (-(2 * Real.pi * t))) ^ n := by
  have hterm : ∀ n ∈ Finset.range N, ∫ z, w (y - z) ∂(convPow μ n)
      = ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * (charFun μ (-(2 * Real.pi * t))) ^ n := by
    intro n _
    rw [integral_comp_sub_eq_integral_charFun hwc hw hFw y]
    simp only [charFun_convPow]
  rw [Finset.sum_congr rfl hterm,
    ← integral_finsetSum _ (fun n _ => integrable_fourier_mul_charFun_pow hw hFw n y)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  beta_reduce
  rw [Finset.mul_sum]

/-- **The `N → ∞` passage in the truncated Parseval identity.**

For a *difference* kernel `w` — one whose transform is supported in `[-T,T]` and
vanishes to first order at the origin, `‖𝓕w(t)‖ ≤ L|t|` — the partial sums of the
smoothed renewal series converge to the resolvent integral

`∑_{n<N} ∫ w(y−z) μ^{*n}(dz) → ∫ 𝓕w(t) e^{2πity} (1 − χ(−2πt))⁻¹ dt`.

Dominated convergence. Off the origin `‖χ‖ < 1`
(`norm_charFun_lt_one_of_nonlattice`), so the geometric partial sums converge
pointwise to `(1 − χ)⁻¹`; the origin is a null set. The dominator is the *constant*
`2C` on `[-T,T]` and `0` outside: `‖∑_{n<N} χⁿ‖ ≤ 2/‖1 − χ‖` by `geom_sum_eq`
together with `‖χ^N‖ ≤ 1`, while `‖𝓕w(t)‖ ≤ C‖1 − χ‖` by
`exists_norm_fourier_le_norm_one_sub_charFun`, and the pole cancels. This is
precisely where the first-order vanishing of `𝓕w` is indispensable: for a general
kernel the limit integrand behaves like `1/(m̂|t|)` near `0`, which is not
integrable in one dimension. -/
theorem tendsto_sum_integral_comp_sub {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) {w : ℝ → ℂ} {T L : ℝ}
    (hwc : Continuous w) (hw : Integrable w) (hFw : Integrable (𝓕 w)) (hL0 : 0 ≤ L)
    (hT : ∀ t : ℝ, T < |t| → 𝓕 w t = 0) (hL : ∀ t : ℝ, ‖𝓕 w t‖ ≤ L * |t|) (y : ℝ) :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, ∫ z, w (y - z) ∂(convPow μ n))
      Filter.atTop
      (nhds (∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * (1 - charFun μ (-(2 * Real.pi * t)))⁻¹)) := by
  obtain ⟨C, hC0, hCb⟩ := exists_norm_fourier_le_norm_one_sub_charFun hμ hint hm hL0 hT hL
  have hFwc : Continuous (𝓕 w) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hw
  have hexp : ∀ t : ℝ, ‖Complex.exp ((2 : ℂ) * Real.pi * t * y * Complex.I)‖ = 1 := by
    intro t
    have hcast : ((2 : ℂ) * Real.pi * t * y * Complex.I)
        = ((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I := by push_cast <;> ring
    rw [hcast, Complex.norm_exp_ofReal_mul_I]
  simp only [sum_integral_comp_sub_eq hwc hw hFw]
  refine tendsto_integral_of_dominated_convergence
    ((Set.Icc (-T) T).indicator (fun _ => 2 * C)) (fun N => ?_) ?_ (fun N => ?_) ?_
  · exact ((hFwc.mul (Complex.continuous_exp.comp (by fun_prop))).mul
      (continuous_finsetSum _ fun n _ =>
        (continuous_charFun.comp (by fun_prop)).pow n)).aestronglyMeasurable
  · exact IntegrableOn.integrable_indicator
      (integrableOn_const measure_Icc_lt_top.ne (by finiteness)) measurableSet_Icc
  · refine Filter.Eventually.of_forall fun t => ?_
    -- the uniform-in-`N` bound `2C`, valid on all of `[-T,T]`
    have hbound : ‖𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * ∑ n ∈ Finset.range N, (charFun μ (-(2 * Real.pi * t))) ^ n‖ ≤ 2 * C := by
      set χ : ℂ := charFun μ (-(2 * Real.pi * t)) with hχ
      rw [norm_mul, norm_mul, hexp t, mul_one]
      by_cases h1 : χ = 1
      · have hz : ‖𝓕 w t‖ ≤ C * ‖1 - χ‖ := hCb t
        rw [h1, sub_self, norm_zero, mul_zero] at hz
        have h0 : ‖𝓕 w t‖ = 0 := le_antisymm hz (norm_nonneg _)
        rw [h0, zero_mul]
        positivity
      · have hd0 : 0 < ‖1 - χ‖ := by
          rw [norm_pos_iff]
          exact fun h => h1 (by linear_combination -h)
        have hnum : ‖χ ^ N - 1‖ ≤ 2 :=
          calc ‖χ ^ N - 1‖ ≤ ‖χ ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ ≤ 1 + 1 := by
                gcongr
                · rw [norm_pow]
                  exact pow_le_one₀ (norm_nonneg _) (norm_charFun_le_one _)
                · simp
            _ = 2 := by norm_num
        rw [geom_sum_eq h1, norm_div, norm_sub_rev χ 1]
        calc ‖𝓕 w t‖ * (‖χ ^ N - 1‖ / ‖1 - χ‖)
            ≤ (C * ‖1 - χ‖) * (2 / ‖1 - χ‖) :=
              mul_le_mul (hCb t) (by gcongr) (by positivity) (by positivity)
          _ = 2 * C := by field_simp
    by_cases hin : t ∈ Set.Icc (-T) T
    · rw [Set.indicator_of_mem hin]
      exact hbound
    · have hout : T < |t| := lt_of_not_ge fun h => hin (Set.mem_Icc.2 (abs_le.1 h))
      rw [Set.indicator_of_notMem hin, hT t hout]
      simp
  · have h0 : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff]
    filter_upwards [h0] with t ht
    have hne : -(2 * Real.pi * t) ≠ 0 := by
      simp [ht, Real.pi_ne_zero]
    exact ((hasSum_geometric_of_norm_lt_one
      (norm_charFun_lt_one_of_nonlattice hμ hne)).tendsto_sum_nat).const_mul _

/-- **Riemann–Lebesgue on the resolvent integrand.**

The limit produced by `tendsto_sum_integral_comp_sub` is, as a function of `y`,
literally the Fourier transform of the resolvent `t ↦ 𝓕w(t)(1 − χ(−2πt))⁻¹`
evaluated at `−y`, so it vanishes as `|y| → ∞`. Mathlib's Riemann–Lebesgue lemma
`Real.zero_at_infty_fourier` is unconditional (for a non-integrable integrand the
transform is identically the junk value `0`), so no hypothesis on `w` or `μ` is
needed here; the integrability that makes the statement non-vacuous is supplied
by the difference-kernel bound of
`exists_norm_fourier_le_norm_one_sub_charFun`. -/
theorem tendsto_integral_fourier_resolvent (μ : Measure ℝ) [IsProbabilityMeasure μ] (w : ℝ → ℂ) :
    Filter.Tendsto (fun y : ℝ => ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * (1 - charFun μ (-(2 * Real.pi * t)))⁻¹)
      (Filter.cocompact ℝ) (nhds 0) := by
  have hrw : ∀ y : ℝ, (∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
      * (1 - charFun μ (-(2 * Real.pi * t)))⁻¹)
      = 𝓕 (fun t : ℝ => 𝓕 w t * (1 - charFun μ (-(2 * Real.pi * t)))⁻¹) (-y) := by
    intro y
    rw [Real.fourier_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Real.inner_apply, smul_eq_mul]
    have hce : Complex.exp (((-2 * Real.pi * (t * -y) : ℝ) : ℂ) * Complex.I)
        = Complex.exp (2 * Real.pi * t * y * Complex.I) := by
      congr 1; push_cast <;> ring
    rw [hce]; ring
  have hneg : Filter.Tendsto (fun y : ℝ => -y) (Filter.cocompact ℝ) (Filter.cocompact ℝ) := by
    rw [cocompact_eq_atBot_atTop]
    exact Filter.tendsto_sup.2 ⟨Filter.tendsto_neg_atBot_atTop.mono_right le_sup_right,
      Filter.tendsto_neg_atTop_atBot.mono_right le_sup_left⟩
  simp only [hrw]
  exact (Real.zero_at_infty_fourier _).comp hneg

/-- **Blackwell's theorem for difference kernels** (A-4g-3).

If, for every `y`, the smoothed renewal series `∑ₙ ∫ w(y−z) μ^{*n}(dz)` converges
to `S y`, then `S y → 0` as `y → ∞`, for a kernel `w` whose transform is supported
in `[-T,T]` and vanishes to first order at the origin. This is the paper's
conclusion `∫ w dU → (∫ w)/m̂` in the case `∫ w = 0`; the constant `1/m̂` for a
general kernel is identified separately, from the subtracted pole. -/
theorem tendsto_zero_of_tendsto_sum_integral_comp_sub {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) {w : ℝ → ℂ} {T L : ℝ}
    (hwc : Continuous w) (hw : Integrable w) (hFw : Integrable (𝓕 w)) (hL0 : 0 ≤ L)
    (hT : ∀ t : ℝ, T < |t| → 𝓕 w t = 0) (hL : ∀ t : ℝ, ‖𝓕 w t‖ ≤ L * |t|) {S : ℝ → ℂ}
    (hS : ∀ y : ℝ, Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, ∫ z, w (y - z) ∂(convPow μ n))
      Filter.atTop (nhds (S y))) :
    Filter.Tendsto S Filter.atTop (nhds 0) := by
  have hval : ∀ y : ℝ, S y = ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
      * (1 - charFun μ (-(2 * Real.pi * t)))⁻¹ := fun y =>
    tendsto_nhds_unique (hS y)
      (tendsto_sum_integral_comp_sub hμ hint hm hwc hw hFw hL0 hT hL y)
  rw [funext hval]
  exact (tendsto_integral_fourier_resolvent μ w).mono_left
    (by rw [cocompact_eq_atBot_atTop]; exact le_sup_right)

/-!
### The directly-Riemann-integrable norm and the cell error estimate

The key renewal theorem is proved here by *approximation in the d.R.i. norm*
rather than by Feller's route through Blackwell's interval theorem. The whole
mechanism is one inequality: if the renewal measure of every unit cell is at most
`C`, then the entire smoothed renewal series of a kernel `g` is at most
`C · ‖g‖_DRI`, where

  `‖g‖_DRI := ∑_{k ∈ ℤ} sup_{[k, k+1]} g`.

Applied to `g = |z − w|` this bounds the error made by replacing a d.R.i. kernel
`z` with a bandlimited approximation `w`; applied to `g = |z|` it gives absolute
convergence of the series itself.

Everything here is stated in `ℝ≥0∞`, where suprema and sums are total and the
inequality needs no integrability, measurability or finiteness hypotheses at all.
The real-valued consequences are extracted at the point of use.
-/

lemma le_cellSup {g : ℝ → ℝ≥0∞} {k : ℤ} {x : ℝ} (hx : x ∈ Set.Icc (k : ℝ) (k + 1)) :
    g x ≤ cellSup g k :=
  le_iSup₂ (f := fun x (_ : x ∈ Set.Icc (k : ℝ) (k + 1)) => g x) x hx

lemma driNorm_def (g : ℝ → ℝ≥0∞) : driNorm g = ∑' k : ℤ, cellSup g k := rfl

lemma cellSup_mono {g h : ℝ → ℝ≥0∞} (hgh : ∀ x, g x ≤ h x) (k : ℤ) :
    cellSup g k ≤ cellSup h k :=
  iSup₂_mono fun x _ => hgh x

lemma driNorm_mono {g h : ℝ → ℝ≥0∞} (hgh : ∀ x, g x ≤ h x) : driNorm g ≤ driNorm h :=
  ENNReal.tsum_le_tsum (cellSup_mono hgh)

lemma cellSup_add_le (g h : ℝ → ℝ≥0∞) (k : ℤ) :
    cellSup (fun x => g x + h x) k ≤ cellSup g k + cellSup h k :=
  iSup₂_le fun _ hx => add_le_add (le_cellSup hx) (le_cellSup hx)

/-- `‖·‖_DRI` is subadditive: a supremum of a sum is at most the sum of the
suprema, cellwise. -/
lemma driNorm_add_le (g h : ℝ → ℝ≥0∞) : driNorm (fun x => g x + h x) ≤ driNorm g + driNorm h := by
  rw [driNorm_def, driNorm_def, driNorm_def, ← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum (cellSup_add_le g h)

/-- **An approximant of a d.R.i. kernel is itself d.R.i.**

`‖v‖_DRI ≤ ‖z‖_DRI + ‖z − v‖_DRI`, since `v = z − (z − v)` pointwise. This is how
the assembly gets finiteness of `‖w ⋆ K_a‖_DRI` for free: the approximation error
is already known to be small, hence finite, and `z` is d.R.i. by hypothesis — so
no separate cell analysis of the approximant is needed. -/
lemma driNorm_enorm_le_add_sub (z v : ℝ → ℂ) :
    driNorm (fun x => ‖v x‖ₑ)
      ≤ driNorm (fun x => ‖z x‖ₑ) + driNorm (fun x => ‖z x - v x‖ₑ) := by
  refine le_trans (driNorm_mono fun x => ?_) (driNorm_add_le _ _)
  have h : ‖z x - (z x - v x)‖ₑ ≤ ‖z x‖ₑ + ‖z x - v x‖ₑ := enorm_sub_le
  rwa [sub_sub_cancel] at h

/-- Chaining two approximations: `‖z − v‖_DRI ≤ ‖z − w‖_DRI + ‖w − v‖_DRI`.
The route composes a cutoff `z ⇝ w` with a smoothing `w ⇝ v`, and this is what
adds the two errors. -/
lemma driNorm_enorm_sub_le_add (z w v : ℝ → ℂ) :
    driNorm (fun x => ‖z x - v x‖ₑ)
      ≤ driNorm (fun x => ‖z x - w x‖ₑ) + driNorm (fun x => ‖w x - v x‖ₑ) := by
  refine le_trans (driNorm_mono fun x => ?_) (driNorm_add_le _ _)
  have h : ‖(z x - w x) + (w x - v x)‖ₑ ≤ ‖z x - w x‖ₑ + ‖w x - v x‖ₑ := enorm_add_le _ _
  rwa [sub_add_sub_cancel] at h

/-- **The d.R.i. tail vanishes**: for a kernel of finite d.R.i. norm, the mass
carried by the cells outside `[-N, N]` tends to `0`.

This is the quantitative content of "`z` is directly Riemann integrable" that the
cutoff step consumes: truncating `z` outside a large interval costs exactly this
tail, so the truncation error can be made arbitrarily small in `‖·‖_DRI`.

Reduced to `ENNReal.tendsto_tsum_compl_atTop_zero`, whose index filter is
`atTop` over *finite sets* of `ℤ`; the bridge is that any finite `S ⊆ ℤ` is
contained in some `Finset.Icc (-N) N` (take `N = S.sup Int.natAbs`), and
`{k | N < |k|}` is exactly the complement of that interval. -/
theorem tendsto_driNorm_tail {g : ℝ → ℝ≥0∞} (hg : driNorm g ≠ ∞) :
    Filter.Tendsto (fun N : ℕ => ∑' k : ℤ, Set.indicator {k : ℤ | (N : ℤ) < |k|} (cellSup g) k)
      Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have h := ENNReal.tendsto_nhds_zero.1 (ENNReal.tendsto_tsum_compl_atTop_zero hg) ε hε
  obtain ⟨S, hS⟩ := Filter.eventually_atTop.1 h
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, S ⊆ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) := by
    refine ⟨S.sup Int.natAbs, fun k hk => ?_⟩
    have hk' : k.natAbs ≤ S.sup Int.natAbs := Finset.le_sup hk
    rw [Finset.mem_Icc]
    omega
  refine Filter.eventually_atTop.2 ⟨N₀, fun N hN => ?_⟩
  have hsub : S ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    refine hN₀.trans (Finset.Icc_subset_Icc ?_ ?_) <;> [skip; skip] <;>
      exact_mod_cast by omega
  have hkey := hS (Finset.Icc (-(N : ℤ)) (N : ℤ)) hsub
  have hset : {k : ℤ | (N : ℤ) < |k|} = ((Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset ℤ) : Set ℤ)ᶜ := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Finset.coe_Icc, Set.mem_Icc]
    rw [← not_le, abs_le]
  rw [hset, ← tsum_subtype]
  exact hkey

/-- The unit cells `[y−k−1, y−k)`, `k ∈ ℤ`, are pairwise disjoint and cover `ℝ`;
they are the cells of the previous decomposition pulled back through `s ↦ y − s`,
so that `y − s` ranges over `(k, k+1] ⊆ [k, k+1]` on the `k`-th one. -/
private lemma iUnion_shiftedCell (y : ℝ) : (⋃ k : ℤ, Set.Ico (y - k - 1) (y - k)) = Set.univ := by
  refine Set.eq_univ_of_forall fun s => ?_
  refine Set.mem_iUnion.2 ⟨⌈y - s⌉ - 1, ?_⟩
  have h1 : y - s ≤ (⌈y - s⌉ : ℝ) := Int.le_ceil _
  have h2 : (⌈y - s⌉ : ℝ) < y - s + 1 := Int.ceil_lt_add_one _
  simp only [Set.mem_Ico]
  push_cast
  constructor <;> linarith

private lemma pairwise_disjoint_shiftedCell (y : ℝ) :
    Pairwise (Function.onFun Disjoint fun k : ℤ => Set.Ico (y - k - 1) (y - k)) := by
  have key : ∀ k l : ℤ, k < l →
      Disjoint (Set.Ico (y - k - 1) (y - k)) (Set.Ico (y - l - 1) (y - l)) := by
    intro k l hkl
    have hle : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast Int.add_one_le_iff.2 hkl
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    simp only [Set.mem_Ico] at hx hx'
    linarith [hx.1, hx'.2]
  intro k l hkl
  rcases hkl.lt_or_gt with h | h
  · exact key k l h
  · exact (key l k h).symm

/-! #### A reference profile of finite d.R.i. norm

`(1+x²)⁻¹` is the profile every far-field estimate is compared against: it has
finite d.R.i. norm, so any kernel dominated by a constant multiple of it has one
too. This is what makes the far cells of a smoothing summable. -/

lemma summable_inv_one_add_sq_int : Summable fun k : ℤ => (1 + ((k : ℝ)) ^ 2)⁻¹ := by
  have hnat : Summable fun n : ℕ => (1 + ((n : ℝ)) ^ 2)⁻¹ := by
    have h0 : Summable fun n : ℕ => 1 / ((n : ℝ)) ^ 2 :=
      Real.summable_one_div_nat_pow.2 one_lt_two
    have h1 : Summable fun n : ℕ => 2 * (1 / (((n : ℝ)) + 1) ^ 2) := by
      refine Summable.mul_left 2 ?_
      have := (summable_nat_add_iff 1).2 h0
      simpa using this
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h1
    rw [inv_eq_one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ((n : ℝ) - 1), Nat.cast_nonneg (α := ℝ) n]
  exact Summable.of_nat_of_neg (by simpa using hnat) (by simpa using hnat)

/-- **The reference profile has finite d.R.i. norm.**

On the cell `[k, k+1]` the profile is at most `8(1+k²)⁻¹` — the constant `8`
absorbs the worst case `k = −1`, where the cell reaches the origin — and
`∑_{k∈ℤ}(1+k²)⁻¹` converges. -/
theorem driNorm_ofReal_inv_one_add_sq_ne_top :
    driNorm (fun x : ℝ => ENNReal.ofReal (1 + x ^ 2)⁻¹) ≠ ∞ := by
  have hcell : ∀ k : ℤ, cellSup (fun x : ℝ => ENNReal.ofReal (1 + x ^ 2)⁻¹) k
      ≤ ENNReal.ofReal (8 * (1 + ((k : ℝ)) ^ 2)⁻¹) := by
    intro k
    refine iSup₂_le fun x hx => ENNReal.ofReal_le_ofReal ?_
    rw [Set.mem_Icc] at hx
    have hx2 : 1 + ((k : ℝ)) ^ 2 ≤ 8 * (1 + x ^ 2) := by
      rcases le_or_gt 0 ((k : ℝ)) with hk | hk
      · nlinarith [hx.1, sq_nonneg x]
      · nlinarith [hx.2, sq_nonneg (x + 1)]
    rw [show (8 : ℝ) * (1 + ((k : ℝ)) ^ 2)⁻¹ = 8 / (1 + ((k : ℝ)) ^ 2) by ring,
      show ((1 : ℝ) + x ^ 2)⁻¹ = 1 / (1 + x ^ 2) by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hcell)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
    (summable_inv_one_add_sq_int.mul_left 8)]
  exact ENNReal.ofReal_ne_top

/-! #### The d.R.i. norm dominates the `L¹` norm

The cells have Lebesgue measure `1`, so `∫g ≤ ∑_k sup_{cell k} g = ‖g‖_DRI`
directly. Two things follow, both needed by the assembly: a kernel of finite
d.R.i. norm is integrable, and `∫` is `‖·‖_DRI`-continuous — so the approximation
that transfers the renewal limit also transfers the constant `∫z` in it. -/

private lemma iUnion_cell : (⋃ k : ℤ, Set.Ico (k : ℝ) (k + 1)) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  refine Set.mem_iUnion.2 ⟨⌊x⌋, ?_⟩
  simp only [Set.mem_Ico]
  exact ⟨Int.floor_le x, Int.lt_floor_add_one x⟩

private lemma pairwise_disjoint_cell :
    Pairwise (Function.onFun Disjoint fun k : ℤ => Set.Ico (k : ℝ) (k + 1)) := by
  have key : ∀ k l : ℤ, k < l → Disjoint (Set.Ico (k : ℝ) (k + 1)) (Set.Ico (l : ℝ) (l + 1)) := by
    intro k l hkl
    have hle : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast Int.add_one_le_iff.2 hkl
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    simp only [Set.mem_Ico] at hx hx'
    linarith [hx.2, hx'.1]
  intro k l hkl
  rcases hkl.lt_or_gt with h | h
  · exact key k l h
  · exact (key l k h).symm

/-- **`‖g‖_{L¹} ≤ ‖g‖_DRI`**: the unit cells have Lebesgue measure `1`. -/
theorem lintegral_le_driNorm (g : ℝ → ℝ≥0∞) : ∫⁻ x, g x ≤ driNorm g := by
  calc ∫⁻ x, g x = ∫⁻ x in ⋃ k : ℤ, Set.Ico (k : ℝ) (k + 1), g x := by
        rw [iUnion_cell, Measure.restrict_univ]
    _ = ∑' k : ℤ, ∫⁻ x in Set.Ico (k : ℝ) (k + 1), g x :=
        lintegral_iUnion (fun _ => measurableSet_Ico) pairwise_disjoint_cell _
    _ ≤ ∑' k : ℤ, cellSup g k := ENNReal.tsum_le_tsum fun k => ?_
    _ = driNorm g := rfl
  calc ∫⁻ x in Set.Ico (k : ℝ) (k + 1), g x
      ≤ ∫⁻ _x in Set.Ico (k : ℝ) (k + 1), cellSup g k :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ico).2 (.of_forall fun x hx =>
          le_cellSup ⟨hx.1, hx.2.le⟩))
    _ = cellSup g k * volume (Set.Ico (k : ℝ) (k + 1)) := setLIntegral_const _ _
    _ = cellSup g k := by rw [Real.volume_Ico, add_sub_cancel_left]; simp

/-- A kernel of finite d.R.i. norm is integrable. -/
theorem integrable_of_driNorm {z : ℝ → ℂ} (hz : Continuous z)
    (hdri : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) : Integrable z :=
  ⟨hz.aestronglyMeasurable, lt_of_le_of_lt (lintegral_le_driNorm _) (lt_top_iff_ne_top.2 hdri)⟩

/-- `∫` is continuous in the d.R.i. norm: the constant appearing in the renewal
limit moves with the approximation. -/
theorem norm_integral_sub_le_driNorm {z w : ℝ → ℂ} (hz : Integrable z) (hw : Integrable w)
    (hdri : driNorm (fun x => ‖z x - w x‖ₑ) ≠ ∞) :
    ‖(∫ x, z x) - ∫ x, w x‖ ≤ (driNorm (fun x => ‖z x - w x‖ₑ)).toReal := by
  rw [← integral_sub hz hw]
  refine (ENNReal.ofReal_le_iff_le_toReal hdri).1 ?_
  rw [ofReal_norm]
  exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_le_driNorm _)

/-! #### The cutoff

The first half of the bandlimited approximation: replace a d.R.i. kernel by a
*compactly supported* one, at a cost equal to the tail of `tendsto_driNorm_tail`.
Multiplying by a continuous plateau, rather than by an indicator, keeps the
approximant continuous, which the convolution step needs. -/

lemma continuous_cutoff (M : ℝ) : Continuous (cutoff M) :=
  continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs))

lemma cutoff_nonneg (M x : ℝ) : 0 ≤ cutoff M x := le_max_left _ _

lemma cutoff_le_one (M x : ℝ) : cutoff M x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma cutoff_eq_one {M x : ℝ} (hx : |x| ≤ M) : cutoff M x = 1 := by
  rw [cutoff, min_eq_left (by linarith), max_eq_right zero_le_one]

lemma cutoff_eq_zero {M x : ℝ} (hx : M + 1 ≤ |x|) : cutoff M x = 0 := by
  rw [cutoff, min_eq_right (by linarith), max_eq_left (by linarith)]

/-- **The cutoff step** (A-5b-2): a continuous kernel of finite d.R.i. norm is
approximated, to any accuracy in `‖·‖_DRI`, by a continuous kernel with *compact
support*.

The approximant is `z·χ_M`, which agrees with `z` on `[-M, M]` and is dominated by
`z` everywhere, so the error is supported on the cells outside `[-M, M]` and is
bounded there by `z`'s own cell suprema — exactly the tail that
`tendsto_driNorm_tail` sends to `0`. -/
theorem exists_hasCompactSupport_driNorm_sub_lt {z : ℝ → ℂ} (hz : Continuous z)
    (hdri : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ w : ℝ → ℂ, Continuous w ∧ HasCompactSupport w ∧ (∀ x, ‖w x‖ₑ ≤ ‖z x‖ₑ) ∧
      driNorm (fun x => ‖z x - w x‖ₑ) < ε := by
  obtain ⟨N, hN⟩ := ((tendsto_driNorm_tail hdri).eventually_lt_const hε).exists
  set M : ℝ := (N : ℝ) + 1 with hM
  refine ⟨fun x => (cutoff M x : ℂ) * z x, ?_, ?_, ?_, ?_⟩
  · exact (Complex.continuous_ofReal.comp (continuous_cutoff M)).mul hz
  · refine HasCompactSupport.intro (isCompact_Icc (a := -(M + 1)) (b := M + 1)) fun x hx => ?_
    have habs : M + 1 ≤ |x| := by
      rcases abs_cases x with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [Set.mem_Icc, not_and_or] at hx <;>
        rcases hx with h | h <;> [linarith; linarith; linarith; linarith]
    rw [cutoff_eq_zero habs]
    simp
  · intro x
    rw [enorm_mul]
    refine mul_le_of_le_one_left' ?_
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg M x)]
    exact ENNReal.ofReal_le_one.2 (cutoff_le_one M x)
  · refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun k => ?_) hN
    by_cases hk : (N : ℤ) < |k|
    · rw [Set.indicator_apply, if_pos (show k ∈ {k : ℤ | (N : ℤ) < |k|} from hk)]
      refine cellSup_mono (fun x => ?_) k
      rw [show z x - (cutoff M x : ℂ) * z x = ((1 - cutoff M x : ℝ) : ℂ) * z x by push_cast; ring,
        enorm_mul]
      refine mul_le_of_le_one_left' ?_
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [cutoff_le_one M x])]
      exact ENNReal.ofReal_le_one.2 (by linarith [cutoff_nonneg M x])
    · rw [Set.indicator_apply, if_neg (show k ∉ {k : ℤ | (N : ℤ) < |k|} from hk),
        nonpos_iff_eq_zero]
      refine iSup₂_eq_bot.2 fun x hx => ?_
      obtain ⟨h1, h2⟩ := abs_le.1 (not_lt.1 hk)
      have habs : |x| ≤ M := by
        rw [Set.mem_Icc] at hx
        have h1' : -(N : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
        have h2' : ((k : ℝ)) ≤ (N : ℝ) := by exact_mod_cast h2
        rw [abs_le]
        constructor <;> [linarith [hx.1]; linarith [hx.2]]
      have hzero : z x - ((cutoff M x : ℝ) : ℂ) * z x = 0 := by
        rw [cutoff_eq_one habs]; push_cast <;> ring
      simp [hzero]

/-- **The cell error estimate** (A-5a): a uniform bound `C` on the renewal measure
of unit cells turns the smoothed renewal series into a `C`-multiple of the
d.R.i. norm,

  `∫ g(y − s) U(ds) ≤ C · ‖g‖_DRI`,   uniformly in `y`.

Decompose `ℝ` into the cells `[y−k−1, y−k)`, on which `y − s ∈ (k, k+1]`, bound
`g` there by its cell supremum, and bound each cell's `U`-mass by `C`. Nothing
about `μ` is used beyond the hypothesis `hC`, which
`exists_bound_renewalMeasure_Icc_of_expTransform` supplies. -/
theorem lintegral_comp_sub_renewalMeasure_le {μ : Measure ℝ} [SFinite μ] {C : ℝ≥0∞}
    (hC : ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + 1)) ≤ C) (g : ℝ → ℝ≥0∞) (y : ℝ) :
    ∫⁻ s, g (y - s) ∂(renewalMeasure μ) ≤ C * driNorm g := by
  have hcell : ∀ k : ℤ,
      ∫⁻ s in Set.Ico (y - k - 1) (y - k), g (y - s) ∂(renewalMeasure μ)
        ≤ cellSup g k * C := by
    intro k
    have hmem : ∀ s ∈ Set.Ico (y - (k : ℝ) - 1) (y - k), y - s ∈ Set.Icc (k : ℝ) (k + 1) := by
      intro s hs
      simp only [Set.mem_Ico] at hs
      exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
    calc ∫⁻ s in Set.Ico (y - (k : ℝ) - 1) (y - k), g (y - s) ∂(renewalMeasure μ)
        ≤ ∫⁻ _s in Set.Ico (y - (k : ℝ) - 1) (y - k), cellSup g k ∂(renewalMeasure μ) :=
          lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ico).2
            (.of_forall fun s hs => le_cellSup (hmem s hs)))
      _ = cellSup g k * renewalMeasure μ (Set.Ico (y - (k : ℝ) - 1) (y - k)) :=
          setLIntegral_const _ _
      _ ≤ cellSup g k * C := by
          refine mul_le_mul' le_rfl ((measure_mono ?_).trans (hC (y - (k : ℝ) - 1)))
          exact Set.Ico_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl (by linarith))
  calc ∫⁻ s, g (y - s) ∂(renewalMeasure μ)
      = ∫⁻ s in ⋃ k : ℤ, Set.Ico (y - (k : ℝ) - 1) (y - k), g (y - s) ∂(renewalMeasure μ) := by
        rw [iUnion_shiftedCell, Measure.restrict_univ]
    _ = ∑' k : ℤ, ∫⁻ s in Set.Ico (y - (k : ℝ) - 1) (y - k), g (y - s) ∂(renewalMeasure μ) :=
        lintegral_iUnion (fun _ => measurableSet_Ico) (pairwise_disjoint_shiftedCell y) _
    _ ≤ ∑' k : ℤ, cellSup g k * C := ENNReal.tsum_le_tsum hcell
    _ = (∑' k : ℤ, cellSup g k) * C := ENNReal.tsum_mul_right
    _ = C * driNorm g := by rw [driNorm_def, mul_comm]

/-- The same bound on each convolution power's series, which is what the
real-valued statements consume: `∑ₙ ∫ g(y−s) μ^{*n}(ds) ≤ C‖g‖_DRI`. -/
theorem tsum_lintegral_comp_sub_le {μ : Measure ℝ} [SFinite μ] {C : ℝ≥0∞}
    (hC : ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + 1)) ≤ C) (g : ℝ → ℝ≥0∞) (y : ℝ) :
    ∑' n, ∫⁻ s, g (y - s) ∂(convPow μ n) ≤ C * driNorm g := by
  rw [← lintegral_renewalMeasure]
  exact lintegral_comp_sub_renewalMeasure_le hC g y

/-- Each convolution power integrates `z(y − ·)` absolutely, as soon as `z` is
measurable with finite d.R.i. norm and the cells have uniformly bounded `U`-mass:
the `n`-th term of the series bounded in `tsum_lintegral_comp_sub_le` is one
summand of a finite sum. -/
theorem integrable_comp_sub_of_driNorm {μ : Measure ℝ} [SFinite μ] {C : ℝ≥0∞}
    (hC : ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + 1)) ≤ C) (hCfin : C ≠ ∞)
    {z : ℝ → ℂ} (hz : Continuous z) (hdri : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) (y : ℝ) (n : ℕ) :
    Integrable (fun s => z (y - s)) (convPow μ n) := by
  refine ⟨(hz.comp (continuous_const.sub continuous_id)).aestronglyMeasurable, ?_⟩
  have hser : ∑' k, ∫⁻ s, ‖z (y - s)‖ₑ ∂(convPow μ k) ≤ C * driNorm (fun x => ‖z x‖ₑ) :=
    tsum_lintegral_comp_sub_le hC (fun x => ‖z x‖ₑ) y
  refine lt_of_le_of_lt ((ENNReal.le_tsum n).trans hser) ?_
  exact lt_top_iff_ne_top.2 (ENNReal.mul_ne_top hCfin hdri)

/-- The series of `ℝ≥0∞`-norms of the terms is bounded by `C‖z‖_DRI`: the cell
estimate applied after `enorm_integral_le_lintegral_enorm` moves the norm inside
each integral. Everything real-valued below is extracted from this one line. -/
theorem enorm_tsum_integral_comp_sub_le {μ : Measure ℝ} [SFinite μ] {C : ℝ≥0∞}
    (hC : ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + 1)) ≤ C) {z : ℝ → ℂ} (y : ℝ) :
    ∑' n, ‖∫ s, z (y - s) ∂(convPow μ n)‖ₑ ≤ C * driNorm (fun x => ‖z x‖ₑ) :=
  le_trans (ENNReal.tsum_le_tsum fun _ => enorm_integral_le_lintegral_enorm _)
    (tsum_lintegral_comp_sub_le hC (fun x => ‖z x‖ₑ) y)

/-- **Absolute convergence of the smoothed renewal series** (A-5a′): a kernel with
finite d.R.i. norm has a summable renewal series, uniformly bounded in `y`.

This is what discharges the `hS` hypothesis carried by
`tendsto_of_tendsto_sum_integral_comp_sub_sincSq`, which until now had to be
assumed: the limit function `S` exists because the series converges absolutely,
by the cell estimate. -/
theorem summable_norm_integral_comp_sub_of_driNorm {μ : Measure ℝ} [SFinite μ] {C : ℝ≥0∞}
    (hC : ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + 1)) ≤ C) (hCfin : C ≠ ∞)
    {z : ℝ → ℂ} (hdri : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) (y : ℝ) :
    Summable fun n => ‖∫ s, z (y - s) ∂(convPow μ n)‖ := by
  have hne : ∑' n, ‖∫ s, z (y - s) ∂(convPow μ n)‖ₑ ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hCfin hdri)
      (enorm_tsum_integral_comp_sub_le hC y)
  have hnn : Summable fun n => ‖∫ s, z (y - s) ∂(convPow μ n)‖₊ := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable]
    simpa [enorm_eq_nnnorm] using hne
  simpa using NNReal.summable_coe.2 hnn

theorem summable_integral_comp_sub_of_driNorm {μ : Measure ℝ} [SFinite μ] {C : ℝ≥0∞}
    (hC : ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + 1)) ≤ C) (hCfin : C ≠ ∞)
    {z : ℝ → ℂ} (hdri : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) (y : ℝ) :
    Summable fun n => ∫ s, z (y - s) ∂(convPow μ n) :=
  Summable.of_norm (summable_norm_integral_comp_sub_of_driNorm hC hCfin hdri y)

/-- The quantitative half of the previous statement: the series of norms is
bounded by `C‖z‖_DRI`, uniformly in `y`. -/
theorem tsum_norm_integral_comp_sub_le {μ : Measure ℝ} [SFinite μ] {C : ℝ≥0∞}
    (hC : ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + 1)) ≤ C) (hCfin : C ≠ ∞)
    {z : ℝ → ℂ} (hdri : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) (y : ℝ) :
    ∑' n, ‖∫ s, z (y - s) ∂(convPow μ n)‖ ≤ (C * driNorm (fun x => ‖z x‖ₑ)).toReal := by
  refine (ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top hCfin hdri)).1 ?_
  rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _)
    (summable_norm_integral_comp_sub_of_driNorm hC hCfin hdri y)]
  refine le_trans (le_of_eq (tsum_congr fun n => ?_)) (enorm_tsum_integral_comp_sub_le hC y)
  exact ofReal_norm _

/-- **The d.R.i. error estimate** (A-5a′): replacing a kernel `z` by an
approximation `w` perturbs the smoothed renewal series by at most `C‖z−w‖_DRI`,
*uniformly in `y`*.

This is the entire mechanism of the minimal route to the key renewal theorem. The
limit `(∫z)/m̂` is known for bandlimited `w` and `∫w → ∫z` is controlled by the
same norm, so a d.R.i. `z` is squeezed onto its limit by approximating in
`‖·‖_DRI` — with no interval Blackwell and no pointwise sandwich, which is what
makes the pointwise lower kernel (the one obstruction that cannot be built)
unnecessary. -/
theorem norm_tsum_integral_comp_sub_sub_le {μ : Measure ℝ} [SFinite μ] {C : ℝ≥0∞}
    (hC : ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + 1)) ≤ C) (hCfin : C ≠ ∞)
    {z w : ℝ → ℂ} (hz : Continuous z) (hw : Continuous w)
    (hdz : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) (hdw : driNorm (fun x => ‖w x‖ₑ) ≠ ∞)
    (hdzw : driNorm (fun x => ‖z x - w x‖ₑ) ≠ ∞) (y : ℝ) :
    ‖(∑' n, ∫ s, z (y - s) ∂(convPow μ n)) - ∑' n, ∫ s, w (y - s) ∂(convPow μ n)‖
      ≤ (C * driNorm (fun x => ‖z x - w x‖ₑ)).toReal := by
  -- the difference of the two series is the series of the difference kernel
  have hdiff : (∑' n, ∫ s, z (y - s) ∂(convPow μ n)) - ∑' n, ∫ s, w (y - s) ∂(convPow μ n)
      = ∑' n, ∫ s, ((fun x => z x - w x) (y - s)) ∂(convPow μ n) := by
    rw [← (summable_integral_comp_sub_of_driNorm hC hCfin hdz y).tsum_sub
      (summable_integral_comp_sub_of_driNorm hC hCfin hdw y)]
    exact tsum_congr fun n => (integral_sub (integrable_comp_sub_of_driNorm hC hCfin hz hdz y n)
      (integrable_comp_sub_of_driNorm hC hCfin hw hdw y n)).symm
  rw [hdiff]
  refine le_trans (norm_tsum_le_tsum_norm
    (summable_norm_integral_comp_sub_of_driNorm hC hCfin hdzw y)) ?_
  exact tsum_norm_integral_comp_sub_le hC hCfin hdzw y

end Renewal

end AbsorptionCutoff
end

section
-- module Solutions.OAIQ247_JB.Supercritical_RenewalAbel
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Blackwell's theorem by Abel-regularized Fourier inversion

The continuation of `AbsorptionCutoff.Supercritical.Renewal` carrying the Abel argument
that identifies Blackwell's constant `1/m̂`. Split off purely for build time,
exactly as `RenewalKernel` was: the base module had reached ~2500 lines and 70 s
per edit-build cycle, which is too slow for the one-lemma loop.

Nothing here is new mathematics relative to the base module; see
`A4G4_BLACKWELL_PROOF_NOTE.tex` for the argument.

## Main results

* `Renewal.tendsto_tsum_integral_comp_sub`: the reference-kernel renewal limit
  `∑ₙ ∫ v(y−z) μ^{*n}(dz) ⟶ (∫v)/m̂`, for a bounded nonnegative continuous
  bandlimited kernel. **This is where Blackwell's constant is identified.**
* `Renewal.tendsto_of_tendsto_sum_integral_comp_sub_bandlimited`: the same limit
  for a general, possibly signed, bandlimited kernel.
-/

open MeasureTheory
open scoped ENNReal NNReal FourierTransform

namespace AbsorptionCutoff

namespace Renewal

/-!
### Discounted (Abel) Parseval

Everything above is restricted to *difference* kernels, because the undiscounted
resolvent `(1 - χ(-2πt))⁻¹` has a pole at the origin and only the first-order
vanishing of `𝓕w` tames it. Discounting removes the pole outright: for
`0 ≤ r < 1` one has `‖rχ‖ ≤ r < 1`, so `1 - rχ` is bounded away from zero on all
of `ℝ` and the geometric series converges *everywhere*, not merely off a null set.

Consequently the discounted Parseval identity (`eq:abel-parseval` of the proof
note) needs no nonlattice hypothesis, no second moment, no bandlimitedness and no
first-order vanishing — only `w` continuous with `w, 𝓕w ∈ L¹`, exactly the
hypotheses under which Fourier inversion holds pointwise for `w`. The dominating
function in the limit is the honest `L¹` function `‖𝓕w‖ (1-r)⁻¹`, in place of the
compactly supported constant `2C` used for difference kernels.
-/

/-- **The truncated discounted Parseval identity**: the discount factor `rⁿ` rides
along with the `n`-th characteristic-function power, so the geometric ratio
becomes `r χ(-2πt)`. -/
theorem sum_pow_integral_comp_sub_eq {μ : Measure ℝ} [IsProbabilityMeasure μ] {w : ℝ → ℂ}
    (hwc : Continuous w) (hw : Integrable w) (hFw : Integrable (𝓕 w)) (r : ℝ) (N : ℕ) (y : ℝ) :
    ∑ n ∈ Finset.range N, (r : ℂ) ^ n * ∫ z, w (y - z) ∂(convPow μ n)
      = ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * ∑ n ∈ Finset.range N, ((r : ℂ) * charFun μ (-(2 * Real.pi * t))) ^ n := by
  have hterm : ∀ n ∈ Finset.range N, (r : ℂ) ^ n * ∫ z, w (y - z) ∂(convPow μ n)
      = ∫ t : ℝ, (r : ℂ) ^ n * (𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * (charFun μ (-(2 * Real.pi * t))) ^ n) := by
    intro n _
    rw [integral_comp_sub_eq_integral_charFun hwc hw hFw y]
    simp only [charFun_convPow]
    rw [← integral_const_mul]
  rw [Finset.sum_congr rfl hterm,
    ← integral_finsetSum _ (fun n _ => (integrable_fourier_mul_charFun_pow hw hFw n y).const_mul
      ((r : ℂ) ^ n))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  beta_reduce
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_pow]
  ring

/-- **Discounted Parseval** (`eq:abel-parseval`): for `0 ≤ r < 1`,

`∑ₙ rⁿ ∫ w(y−z) μ^{*n}(dz) = ∫ 𝓕w(t) e^{2πity} (1 − r χ(−2πt))⁻¹ dt`,

as a limit of partial sums. Dominated convergence with the `L¹` dominator
`‖𝓕w(t)‖ (1−r)⁻¹`: the partial geometric sums are bounded by `∑ₙ rⁿ = (1−r)⁻¹`
because `‖r χ(−2πt)‖ ≤ r`, and the same bound `r < 1` gives pointwise convergence
of the series to `(1 − r χ)⁻¹` at *every* frequency. There is no singularity in
this identity, which is precisely why the discounted route can see the constant
`1/m̂` that the difference-kernel theorem cannot. -/
theorem tendsto_sum_pow_integral_comp_sub {μ : Measure ℝ} [IsProbabilityMeasure μ] {w : ℝ → ℂ}
    (hwc : Continuous w) (hw : Integrable w) (hFw : Integrable (𝓕 w)) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (y : ℝ) :
    Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, (r : ℂ) ^ n * ∫ z, w (y - z) ∂(convPow μ n))
      Filter.atTop
      (nhds (∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * (1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹)) := by
  have hFwc : Continuous (𝓕 w) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hw
  have hexp : ∀ t : ℝ, ‖Complex.exp ((2 : ℂ) * Real.pi * t * y * Complex.I)‖ = 1 := by
    intro t
    have hcast : ((2 : ℂ) * Real.pi * t * y * Complex.I)
        = ((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I := by push_cast <;> ring
    rw [hcast, Complex.norm_exp_ofReal_mul_I]
  -- the discounted ratio has modulus at most `r`, uniformly in the frequency
  have hnorm : ∀ t : ℝ, ‖(r : ℂ) * charFun μ (-(2 * Real.pi * t))‖ ≤ r := by
    intro t
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
    calc r * ‖charFun μ (-(2 * Real.pi * t))‖ ≤ r * 1 :=
          mul_le_mul_of_nonneg_left (norm_charFun_le_one _) hr0
      _ = r := mul_one r
  simp only [sum_pow_integral_comp_sub_eq hwc hw hFw]
  refine tendsto_integral_of_dominated_convergence
    (fun t => ‖𝓕 w t‖ * (1 - r)⁻¹) (fun N => ?_) (hFw.norm.mul_const _) (fun N => ?_) ?_
  · exact ((hFwc.mul (Complex.continuous_exp.comp (by fun_prop))).mul
      (continuous_finsetSum _ fun n _ =>
        (continuous_const.mul (continuous_charFun.comp (by fun_prop))).pow n)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t => ?_
    rw [norm_mul, norm_mul, hexp t, mul_one]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖∑ n ∈ Finset.range N, ((r : ℂ) * charFun μ (-(2 * Real.pi * t))) ^ n‖
        ≤ ∑ n ∈ Finset.range N, r ^ n := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (hnorm t) n
      _ ≤ (1 - r)⁻¹ := by
          rw [← tsum_geometric_of_lt_one hr0 hr1]
          exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (fun i _ => pow_nonneg hr0 i)
  · refine Filter.Eventually.of_forall fun t => ?_
    exact ((hasSum_geometric_of_norm_lt_one
      (lt_of_le_of_lt (hnorm t) hr1)).tendsto_sum_nat).const_mul _

/-!
### The model pole

The discounted resolvent is compared against the *model denominator*
`b_r(t) = (1-r) + 2π i r m̂ t`, which is what the true denominator
`1 - rχ(-2πt)` looks like to first order. The point of the model is that its
inverse Fourier transform can be computed in closed form, and — crucially — the
answer is **one-sided**: the Laplace representation

`((1-r) + 2π i r m̂ t)⁻¹ = ∫_0^∞ e^{-(1-r)s} e^{-2π i r m̂ t s} ds`

integrates only over `s > 0`, so the resulting kernel lives on `(-∞, y]`. That
one-sidedness is exactly the boundary mass a symmetric principal-value treatment
of the undiscounted pole throws away, and it is why this route recovers the full
constant `1/m̂` rather than `1/(2m̂)` (proof note §§2–3).

The Laplace representation itself is a Mathlib gap: `v4.32.0` has
`integrableOn_exp_mul_complex_Ioi` but no evaluation of `∫_0^∞ e^{-bs} ds` for
complex `b`, so `integral_Ioi_cexp_neg_mul` is proved here from the improper
fundamental theorem of calculus.
-/

/-- `∫_0^∞ e^{-bs} ds = b⁻¹` for `Re b > 0`.

Not in Mathlib v4.32.0 for complex `b`. Proved by the improper FTC
`integral_Ioi_of_hasDerivAt_of_tendsto` applied to the primitive
`s ↦ -b⁻¹ e^{-bs}`, whose modulus `‖b⁻¹‖ e^{-(Re b)s}` vanishes at `+∞`. -/
theorem integral_Ioi_cexp_neg_mul {b : ℂ} (hb : 0 < b.re) :
    ∫ s : ℝ in Set.Ioi (0 : ℝ), Complex.exp (-(b * s)) = b⁻¹ := by
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  set f : ℝ → ℂ := fun s => -b⁻¹ * Complex.exp (-(b * s)) with hf
  have hderiv : ∀ s ∈ Set.Ioi (0 : ℝ), HasDerivAt f (Complex.exp (-(b * s))) s := by
    intro s _
    have h0 : HasDerivAt (fun s : ℝ => b * (s : ℂ)) b s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul b
    have h1 : HasDerivAt (fun s : ℝ => -(b * (s : ℂ))) (-b) s := h0.neg
    have h2 := (h1.cexp).const_mul (-b⁻¹)
    have h3 : -b⁻¹ * (Complex.exp (-(b * s)) * -b) = Complex.exp (-(b * s)) := by field_simp
    rw [← h3]
    exact h2
  have hint : IntegrableOn (fun s : ℝ => Complex.exp (-(b * s))) (Set.Ioi 0) := by
    have := integrableOn_exp_mul_complex_Ioi (a := -b) (by simpa using hb) 0
    simpa [neg_mul] using this
  have hcont : ContinuousWithinAt f (Set.Ici (0 : ℝ)) 0 := by
    apply Continuous.continuousWithinAt
    fun_prop
  have htend : Filter.Tendsto f Filter.atTop (nhds 0) := by
    have hnorm : Filter.Tendsto (fun s : ℝ => ‖f s‖) Filter.atTop (nhds 0) := by
      have hval : ∀ s : ℝ, ‖f s‖ = ‖b⁻¹‖ * Real.exp (-(b.re * s)) := by
        intro s
        rw [hf]
        simp [Complex.norm_exp]
      simp only [hval]
      have h1 : Filter.Tendsto (fun s : ℝ => Real.exp (-(b.re * s))) Filter.atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp
          (Filter.tendsto_neg_atTop_atBot.comp
            (Filter.Tendsto.const_mul_atTop hb Filter.tendsto_id))
      simpa using h1.const_mul ‖b⁻¹‖
    exact tendsto_zero_iff_norm_tendsto_zero.2 hnorm
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend]
  simp [hf]

/-- Pointwise Fourier inversion in the multiplicative form used throughout this
file: `w x = ∫ 𝓕w(t) e^{2πitx} dt`, for `w` continuous with `w, 𝓕w ∈ L¹`.

This is the hypothesis-explicit interface the Abel argument needs; it is the same
computation that opens `integral_comp_sub_eq_integral_charFun`. -/
lemma eq_integral_fourier_mul_exp {w : ℝ → ℂ} (hwc : Continuous w) (hw : Integrable w)
    (hFw : Integrable (𝓕 w)) (x : ℝ) :
    w x = ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * x * Complex.I) := by
  conv_lhs => rw [← congrFun (hwc.fourierInv_fourier_eq hw hFw) x]
  rw [Real.fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Real.inner_apply, smul_eq_mul]
  rw [mul_comm]
  congr 1
  push_cast
  ring_nf

/-- **The model pole is a one-sided exponential average** (`lem:model-pole`,
first identity): for `a > 0` and any `c`,

`∫ 𝓕w(t) e^{2πiyt} (a + 2π i c t)⁻¹ dt = ∫_0^∞ e^{-as} w(y − cs) ds`.

Substitute the Laplace representation `integral_Ioi_cexp_neg_mul` for the
denominator, swap with Fubini (the joint integrand is dominated by
`‖𝓕w(t)‖ e^{-as}`, a product of two integrable functions), and evaluate the
inner frequency integral by pointwise inversion at `y − cs`.

The `s`-integral runs over `(0,∞)` only: at the Abel parameters `a = 1−r`,
`c = r m̂` this is the whole source of the boundary mass. Positivity of `c` is not
needed here; it enters when the substitution `x = y − cs` turns this into an
integral over `(−∞, y]`. -/
theorem integral_fourier_model_pole {w : ℝ → ℂ} (hwc : Continuous w) (hw : Integrable w)
    (hFw : Integrable (𝓕 w)) {a : ℝ} (ha : 0 < a) (c y : ℝ) :
    ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * ((a : ℂ) + 2 * Real.pi * c * t * Complex.I)⁻¹
      = ∫ s in Set.Ioi (0 : ℝ), (Real.exp (-(a * s)) : ℂ) * w (y - c * s) := by
  have hFwc : Continuous (𝓕 w) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hw
  set d : ℝ → ℂ := fun t => (a : ℂ) + 2 * Real.pi * c * t * Complex.I with hd
  have hre : ∀ t : ℝ, 0 < (d t).re := by intro t; simpa [hd] using ha
  set G : ℝ → ℝ → ℂ := fun t s => (Real.exp (-(a * s)) : ℂ) *
    (𝓕 w t * Complex.exp (2 * Real.pi * t * (y - c * s) * Complex.I)) with hG
  have hkey : ∀ t s : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
      * Complex.exp (-(d t * s)) = G t s := by
    intro t s
    calc 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I) * Complex.exp (-(d t * s))
        = 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I + -(d t * s)) := by
          rw [mul_assoc, ← Complex.exp_add]
      _ = 𝓕 w t * Complex.exp (((-(a * s) : ℝ) : ℂ)
            + 2 * Real.pi * t * (y - c * s) * Complex.I) := by
          congr 2
          rw [hd]
          push_cast
          ring
      _ = G t s := by
          rw [hG, Complex.exp_add, ← Complex.ofReal_exp]
          ring
  have hstep : ∀ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I) * (d t)⁻¹
      = ∫ s in Set.Ioi (0 : ℝ), G t s := by
    intro t
    rw [← integral_Ioi_cexp_neg_mul (hre t), ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun s _ => hkey t s
  have hexpint : IntegrableOn (fun s : ℝ => Real.exp (-(a * s))) (Set.Ioi 0) := by
    have := integrableOn_exp_mul_Ioi (a := -a) (by simpa using ha) 0
    simpa [neg_mul] using this
  have hprod : Integrable (Function.uncurry G)
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    have hdom : Integrable (fun p : ℝ × ℝ => ‖𝓕 w p.1‖ * Real.exp (-(a * p.2)))
        (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := Integrable.mul_prod hFw.norm hexpint
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact Continuous.aestronglyMeasurable (by rw [hG]; fun_prop)
    · obtain ⟨t, s⟩ := p
      simp only [Function.uncurry_apply_pair, hG, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      rw [Complex.norm_exp]
      have hz : (2 * (Real.pi : ℂ) * (t : ℂ)
          * ((y : ℂ) - (c : ℂ) * (s : ℂ)) * Complex.I).re = 0 := by simp
      rw [hz]
      simp [mul_comm]
  calc ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I) * (d t)⁻¹
      = ∫ t : ℝ, ∫ s in Set.Ioi (0 : ℝ), G t s :=
        integral_congr_ae (Filter.Eventually.of_forall hstep)
    _ = ∫ s in Set.Ioi (0 : ℝ), ∫ t : ℝ, G t s := integral_integral_swap hprod
    _ = ∫ s in Set.Ioi (0 : ℝ), (Real.exp (-(a * s)) : ℂ) * w (y - c * s) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
        rw [hG, integral_const_mul]
        congr 1
        rw [eq_integral_fourier_mul_exp hwc hw hFw (y - c * s)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        push_cast
        ring_nf

/-- The affine change of variables `x = y - c s` on the whole line, `c > 0`.

Stated for `volume` on `ℝ` via `Measure.integral_comp_mul_left` (the dilation) and
`integral_add_left_eq_self` (the translation); the reflection is absorbed into the
dilation by the *negative* factor `-c`, which avoids needing a
`volume.IsNegInvariant` instance. -/
theorem integral_comp_sub_mul_left (F : ℝ → ℂ) (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ∫ s : ℝ, F (y - c * s) = c⁻¹ • ∫ x : ℝ, F x := by
  have h1 : ∀ s : ℝ, F (y - c * s) = (fun u : ℝ => F (y + u)) ((-c) * s) := by
    intro s; simp only; congr 1; ring
  have h2 : (∫ s : ℝ, F (y - c * s)) = ∫ s : ℝ, (fun u : ℝ => F (y + u)) ((-c) * s) :=
    integral_congr_ae (Filter.Eventually.of_forall h1)
  have h3 := Measure.integral_comp_mul_left (fun u : ℝ => F (y + u)) (-c)
  have h4 : (∫ u : ℝ, F (y + u)) = ∫ x : ℝ, F x := integral_add_left_eq_self F y
  have h5 : |(-c)⁻¹| = c⁻¹ := by rw [abs_inv, abs_neg, abs_of_pos hc]
  rw [h2, h3, h4, h5]

/-- The substitution `x = y - c s`, `c > 0`, turns the one-sided exponential
average over `s > 0` into an integral over the half-line `(-∞, y]`:

`∫_0^∞ e^{-as} w(y − cs) ds = c⁻¹ ∫_{-∞}^y e^{-a(y-x)/c} w(x) dx`.

Both sides are written as full-line integrals of an indicator so that
`integral_comp_sub_mul_left` applies; the two indicator conditions match because
`y − cs < y ↔ s > 0` for `c > 0`. -/
theorem integral_Ioi_exp_comp_sub_eq (w : ℝ → ℂ) {a c : ℝ} (hc : 0 < c) (y : ℝ) :
    ∫ s in Set.Ioi (0 : ℝ), (Real.exp (-(a * s)) : ℂ) * w (y - c * s)
      = c⁻¹ • ∫ x in Set.Iio y, (Real.exp (-(a * (y - x) / c)) : ℂ) * w x := by
  set F : ℝ → ℂ :=
    (Set.Iio y).indicator (fun x => (Real.exp (-(a * (y - x) / c)) : ℂ) * w x) with hF
  have hpt : ∀ s : ℝ, (Set.Ioi (0 : ℝ)).indicator
      (fun s => (Real.exp (-(a * s)) : ℂ) * w (y - c * s)) s = F (y - c * s) := by
    intro s
    by_cases hs : (0 : ℝ) < s
    · have hmem : y - c * s ∈ Set.Iio y := Set.mem_Iio.2 (by nlinarith)
      rw [Set.indicator_of_mem (Set.mem_Ioi.2 hs), hF, Set.indicator_of_mem hmem]
      congr 2
      congr 1
      field_simp
      ring
    · have hmem : y - c * s ∉ Set.Iio y := by
        simp only [Set.mem_Iio, not_lt] at *
        nlinarith
      rw [Set.indicator_of_notMem (by simpa using hs), hF, Set.indicator_of_notMem hmem]
  rw [← integral_indicator measurableSet_Ioi,
    integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_comp_sub_mul_left F y hc, hF, integral_indicator measurableSet_Iio]

/-- **The model pole in closed form** (`eq:model-pole-formula`): for `a, c > 0`,

`∫ 𝓕w(t) e^{2πiyt} (a + 2π i c t)⁻¹ dt
   = c⁻¹ ∫_{-∞}^y e^{-a(y-x)/c} w(x) dx`.

At the Abel parameters `a = 1 − r`, `c = r m̂` the right-hand side is the paper
note's one-sided Laplace kernel; letting `r ↑ 1` at fixed `y` sends the
exponential weight to `1` and leaves `(1/m̂) ∫_{-∞}^y w`. -/
theorem integral_fourier_model_pole_Iio {w : ℝ → ℂ} (hwc : Continuous w) (hw : Integrable w)
    (hFw : Integrable (𝓕 w)) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (y : ℝ) :
    ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * ((a : ℂ) + 2 * Real.pi * c * t * Complex.I)⁻¹
      = c⁻¹ • ∫ x in Set.Iio y, (Real.exp (-(a * (y - x) / c)) : ℂ) * w x := by
  rw [integral_fourier_model_pole hwc hw hFw ha c y, integral_Ioi_exp_comp_sub_eq w hc y]

/-- The exponential weight in the model pole disappears as `r ↑ 1` at fixed `y`.

Dominated convergence on `(-∞, y]` with dominator `‖w‖`: for `0 < r < 1` and
`x < y` the exponent `-(1-r)(y-x)/(rm)` is `≤ 0`, so the weight is bounded by `1`,
and it tends to `1` pointwise because `r ↦ e^{-(1-r)(y-x)/(rm)}` is continuous at
`r = 1` with value `e^0 = 1`. Note the *order of limits*: `y` is fixed here, and
only afterwards is `y → ∞` taken. -/
theorem tendsto_integral_Iio_exp_weight {w : ℝ → ℂ} (hw : Integrable w) {m : ℝ} (hm : 0 < m)
    (y : ℝ) :
    Filter.Tendsto
      (fun r : ℝ => ∫ x in Set.Iio y, (Real.exp (-((1 - r) * (y - x) / (r * m))) : ℂ) * w x)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (∫ x in Set.Iio y, w x)) := by
  have hpos : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), 0 < r :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), r < 1 := eventually_mem_nhdsWithin
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖w x‖) ?_ ?_
    hw.norm.restrict ?_
  · filter_upwards with r
    exact (Continuous.aestronglyMeasurable (by fun_prop)).mul hw.1.restrict
  · filter_upwards [hpos, hlt] with r hr0 hr1
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    have hxy : x < y := hx
    have hexp : Real.exp (-((1 - r) * (y - x) / (r * m))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have h0 : 0 ≤ (1 - r) * (y - x) / (r * m) := by
        apply div_nonneg
        · nlinarith
        · positivity
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    calc Real.exp (-((1 - r) * (y - x) / (r * m))) * ‖w x‖ ≤ 1 * ‖w x‖ :=
          mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
      _ = ‖w x‖ := one_mul _
  · filter_upwards [ae_restrict_mem measurableSet_Iio] with x _
    have hcont : ContinuousAt (fun r : ℝ => (Real.exp (-((1 - r) * (y - x) / (r * m))) : ℂ)) 1 := by
      apply Complex.continuous_ofReal.continuousAt.comp
      apply Real.continuous_exp.continuousAt.comp
      apply ContinuousAt.neg
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      simpa using hm.ne'
    have h0 := hcont.tendsto
    have hval : (Real.exp (-((1 - (1 : ℝ)) * (y - x) / (1 * m))) : ℂ) = 1 := by norm_num
    rw [hval] at h0
    have h1 := h0.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    simpa using h1.mul_const (w x)

/-- **The `r ↑ 1` limit of the model pole** (`eq:model-pole-limit`): at the Abel
parameters `a = 1 − r`, `c = r m̂`,

`∫ 𝓕w(t) e^{2πiyt} ((1−r) + 2π i r m̂ t)⁻¹ dt ⟶ (1/m̂) ∫_{-∞}^y w`

as `r ↑ 1` with `y` held fixed. The limit is taken along `𝓝[<] 1`, on which
`0 < r < 1` holds eventually — exactly the hypotheses
`integral_fourier_model_pole_Iio` needs.

**The order of the two limits is not interchangeable.** First `r ↑ 1` at fixed
`y`, as here; only then `y → ∞`, which turns `∫_{-∞}^y w` into `∫ w` and produces
the constant `(∫w)/m̂`. Swapping them loses the boundary mass and yields
`1/(2m̂)`. -/
theorem tendsto_integral_fourier_model_pole {w : ℝ → ℂ} (hwc : Continuous w) (hw : Integrable w)
    (hFw : Integrable (𝓕 w)) {m : ℝ} (hm : 0 < m) (y : ℝ) :
    Filter.Tendsto (fun r : ℝ => ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * (((1 - r : ℝ) : ℂ) + 2 * Real.pi * ((r * m : ℝ) : ℂ) * t * Complex.I)⁻¹)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (m⁻¹ • ∫ x in Set.Iio y, w x)) := by
  have hpos : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), 0 < r :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), r < 1 := eventually_mem_nhdsWithin
  have hscal : Filter.Tendsto (fun r : ℝ => ((r * m)⁻¹ : ℝ))
      (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds m⁻¹) := by
    have hc : ContinuousAt (fun r : ℝ => (r * m)⁻¹) 1 := by
      apply ContinuousAt.inv₀ (by fun_prop)
      simpa using hm.ne'
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
  have heq : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)),
      (∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * (((1 - r : ℝ) : ℂ) + 2 * Real.pi * ((r * m : ℝ) : ℂ) * t * Complex.I)⁻¹)
      = (r * m)⁻¹ • ∫ x in Set.Iio y, (Real.exp (-((1 - r) * (y - x) / (r * m))) : ℂ) * w x := by
    filter_upwards [hpos, hlt] with r hr0 hr1
    exact integral_fourier_model_pole_Iio hwc hw hFw (by linarith) (by positivity) y
  refine (Filter.tendsto_congr' heq).mpr ?_
  exact hscal.smul (tendsto_integral_Iio_exp_weight hw hm y)

/-!
### Uniform lower bounds on the two denominators

The comparison of the discounted resolvent with the model pole
(`lem:uniform-pole-correction`) rests on the *matching* lower bounds

`‖1 - rχ(u)‖ ≥ c((1-r) + |u|)`,  `‖(1-r) + 2π i r m̂ t‖ ≥ c((1-r) + |t|)`,

valid near the origin and uniformly in `r ∈ [1/2, 1]`. Both are proved the same
way, from `‖z‖ ≥ max(Re z, |Im z|) ≥ (Re z + |Im z|)/2`:

* the real part supplies the `(1-r)` — for the discounted denominator because
  `Re(1 - rχ) = (1-r) + r(1 - Re χ) ≥ 1-r`, using only `Re χ ≤ ‖χ‖ ≤ 1`;
* the imaginary part supplies the `|u|`, from the first-order behaviour
  `Im(1 - χ(u)) = -m̂u + O(u²)`.

The second bullet needs an *imaginary-part* refinement of the A-4f expansion:
`exists_le_norm_one_sub_charFun` bounds the modulus from below, which is not
enough here, because the real part is what carries `(1-r)` and the two
contributions must be separated.
-/

/-- The imaginary part of `1 - charFun μ` has a simple zero at the origin:
`|Im(1 - χ(u))| ≥ (m̂/2)|u|` near `0`, where `m̂ = ∫x dμ > 0`.

Refines `exists_le_norm_one_sub_charFun` (a modulus bound) to the imaginary part,
which is what the Abel comparison needs. Same proof: `|Im z| ≤ ‖z‖` applied to
the `O(u²)` remainder of `exists_norm_one_sub_charFun_add_le`, then the linear
term dominates for `|u|` small. -/
theorem exists_le_abs_im_one_sub_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) :
    ∃ δ > 0, ∀ u : ℝ, |u| ≤ δ →
      (∫ x, x ∂μ) / 2 * |u| ≤ |((1 : ℂ) - charFun μ u).im| := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  obtain ⟨δ, hδ, K, hK, hbound⟩ := exists_norm_one_sub_charFun_add_le hint
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  refine ⟨min δ (m / (2 * (K + 1))), lt_min hδ (by positivity), fun u hu => ?_⟩
  have hu1 : |u| ≤ δ := le_trans hu (min_le_left _ _)
  have hu2 : |u| ≤ m / (2 * (K + 1)) := le_trans hu (min_le_right _ _)
  have hb := hbound u hu1
  have him : |((1 : ℂ) - charFun μ u).im + m * u| ≤ K * u ^ 2 := by
    have h1 : ((1 : ℂ) - charFun μ u + (m : ℂ) * (u : ℂ) * Complex.I).im
        = ((1 : ℂ) - charFun μ u).im + m * u := by simp
    calc |((1 : ℂ) - charFun μ u).im + m * u|
        = |((1 : ℂ) - charFun μ u + (m : ℂ) * (u : ℂ) * Complex.I).im| := by rw [h1]
      _ ≤ ‖(1 : ℂ) - charFun μ u + (m : ℂ) * (u : ℂ) * Complex.I‖ := Complex.abs_im_le_norm _
      _ ≤ K * u ^ 2 := hb
  have habs : K * u ^ 2 ≤ m / 2 * |u| := by
    have hsq : u ^ 2 = |u| * |u| := by rw [← sq_abs u, sq]
    have hmul := mul_le_mul_of_nonneg_left hu2 hK1.le
    have hval : (K + 1) * (m / (2 * (K + 1))) = m / 2 := by field_simp
    rw [hval] at hmul
    calc K * u ^ 2 ≤ (K + 1) * u ^ 2 := by nlinarith [sq_nonneg u]
      _ = ((K + 1) * |u|) * |u| := by rw [hsq]; ring
      _ ≤ (m / 2) * |u| := mul_le_mul_of_nonneg_right hmul (abs_nonneg u)
  have hmu : |m * u| = m * |u| := by rw [abs_mul, abs_of_pos hm]
  have h2 : |m * u| - |((1 : ℂ) - charFun μ u).im| ≤ |((1 : ℂ) - charFun μ u).im + m * u| := by
    calc |m * u| - |((1 : ℂ) - charFun μ u).im|
        = |m * u| - |-((1 : ℂ) - charFun μ u).im| := by rw [abs_neg]
      _ ≤ |m * u - -((1 : ℂ) - charFun μ u).im| := abs_sub_abs_le_abs_sub _ _
      _ = |((1 : ℂ) - charFun μ u).im + m * u| := by rw [sub_neg_eq_add, add_comm]
  rw [hmu] at h2
  linarith

/-- **The discounted denominator is bounded below by `c((1-r) + |u|)`** near the
origin, uniformly for `r ∈ [1/2, 1]` (`eq:true-denominator-lower`).

The real part gives `(1-r)` and the imaginary part gives `|u|`; discounting is
exactly what makes the bound survive at `u = 0`, where the undiscounted
denominator vanishes. -/
theorem exists_le_norm_one_sub_smul_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) :
    ∃ δ > 0, ∀ r : ℝ, 1 / 2 ≤ r → r ≤ 1 → ∀ u : ℝ, |u| ≤ δ →
      min 1 ((∫ x, x ∂μ) / 4) / 2 * ((1 - r) + |u|) ≤ ‖1 - (r : ℂ) * charFun μ u‖ := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  obtain ⟨δ, hδ, him⟩ := exists_le_abs_im_one_sub_charFun hint hm
  refine ⟨δ, hδ, fun r hr hr1 u hu => ?_⟩
  have hr0 : (0 : ℝ) ≤ r := by linarith
  set z : ℂ := 1 - (r : ℂ) * charFun μ u with hz
  have hrec : (1 - r) ≤ z.re := by
    have h1 : (charFun μ u).re ≤ 1 := le_trans (Complex.re_le_norm _) (norm_charFun_le_one _)
    have h2 : z.re = 1 - r * (charFun μ u).re := by simp [hz]
    rw [h2]
    nlinarith
  have hrez : (1 - r) ≤ ‖z‖ := le_trans hrec (Complex.re_le_norm _)
  have himz : m / 4 * |u| ≤ ‖z‖ := by
    have h3 : z.im = r * ((1 : ℂ) - charFun μ u).im := by simp [hz]
    have h4 : |z.im| = r * |((1 : ℂ) - charFun μ u).im| := by
      rw [h3, abs_mul, abs_of_nonneg hr0]
    have h5 : m / 2 * |u| ≤ |((1 : ℂ) - charFun μ u).im| := by
      rw [hmdef]; exact him u hu
    have h6 : m / 4 * |u| ≤ r * (m / 2 * |u|) := by
      have h7 := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ r - 1 / 2) hm.le) (abs_nonneg u)
      nlinarith
    calc m / 4 * |u| ≤ r * (m / 2 * |u|) := h6
      _ ≤ r * |((1 : ℂ) - charFun μ u).im| := mul_le_mul_of_nonneg_left h5 hr0
      _ = |z.im| := h4.symm
      _ ≤ ‖z‖ := Complex.abs_im_le_norm _
  have hmin1 : min 1 (m / 4) ≤ 1 := min_le_left _ _
  have hmin2 : min 1 (m / 4) ≤ m / 4 := min_le_right _ _
  have h1r : 0 ≤ 1 - r := by linarith
  calc min 1 (m / 4) / 2 * ((1 - r) + |u|)
      = (min 1 (m / 4) * (1 - r) + min 1 (m / 4) * |u|) / 2 := by ring
    _ ≤ ((1 - r) + m / 4 * |u|) / 2 := by
        have ha : min 1 (m / 4) * (1 - r) ≤ 1 * (1 - r) :=
          mul_le_mul_of_nonneg_right hmin1 h1r
        have hb : min 1 (m / 4) * |u| ≤ m / 4 * |u| :=
          mul_le_mul_of_nonneg_right hmin2 (abs_nonneg u)
        rw [one_mul] at ha
        linarith
    _ ≤ ‖z‖ := by linarith

/-- **The model denominator obeys the same lower bound**
(`eq:model-denominator-lower`), and unconditionally in `t`: no expansion is
involved, the real part *is* `1-r` and the imaginary part *is* `2π r m̂ t`. -/
theorem le_norm_model_denominator {m : ℝ} (hm : 0 < m) {r : ℝ} (hr : 1 / 2 ≤ r) (hr1 : r ≤ 1)
    (t : ℝ) :
    min 1 (Real.pi * m) / 2 * ((1 - r) + |t|)
      ≤ ‖((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I‖ := by
  set z : ℂ := ((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I
    with hz
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hre : z.re = 1 - r := by simp [hz]
  have him : z.im = 2 * Real.pi * (r * m) * t := by simp [hz]
  have hrez : (1 - r) ≤ ‖z‖ := by rw [← hre]; exact Complex.re_le_norm _
  have himz : Real.pi * m * |t| ≤ ‖z‖ := by
    have h4 : |z.im| = 2 * Real.pi * (r * m) * |t| := by
      rw [him, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * (r * m))]
    have h6 : Real.pi * m * |t| ≤ 2 * Real.pi * (r * m) * |t| := by
      have h7 := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ r - 1 / 2)
        (mul_nonneg Real.pi_pos.le hm.le)) (abs_nonneg t)
      nlinarith
    calc Real.pi * m * |t| ≤ 2 * Real.pi * (r * m) * |t| := h6
      _ = |z.im| := h4.symm
      _ ≤ ‖z‖ := Complex.abs_im_le_norm _
  have hmin1 : min 1 (Real.pi * m) ≤ 1 := min_le_left _ _
  have hmin2 : min 1 (Real.pi * m) ≤ Real.pi * m := min_le_right _ _
  have h1r : 0 ≤ 1 - r := by linarith
  calc min 1 (Real.pi * m) / 2 * ((1 - r) + |t|)
      = (min 1 (Real.pi * m) * (1 - r) + min 1 (Real.pi * m) * |t|) / 2 := by ring
    _ ≤ ((1 - r) + Real.pi * m * |t|) / 2 := by
        have ha : min 1 (Real.pi * m) * (1 - r) ≤ 1 * (1 - r) :=
          mul_le_mul_of_nonneg_right hmin1 h1r
        have hb : min 1 (Real.pi * m) * |t| ≤ Real.pi * m * |t| :=
          mul_le_mul_of_nonneg_right hmin2 (abs_nonneg t)
        rw [one_mul] at ha
        linarith
    _ ≤ ‖z‖ := by linarith

/-- **The corrected resolvent is bounded near the origin, uniformly in `r`**
(`lem:uniform-pole-correction`, the small-frequency regime): for `1/2 ≤ r < 1`
and `|t| ≤ δ`,

`‖(1 - rχ(-2πt))⁻¹ - ((1-r) + 2π i r m̂ t)⁻¹‖ ≤ C`

with `δ, C` independent of `r`.

The two denominators differ by exactly `r q(t)`, where
`q(t) = 1 - χ(-2πt) - 2π i m̂ t` is the second-order remainder of the
characteristic function, so `‖q(t)‖ = O(t²)`; each denominator is
`≳ (1-r) + |t|` by the two lemmas above, so the quotient is
`≲ t²/((1-r)+|t|)² ≤ 1`. Note where the uniformity comes from: the `(1-r)` in the
lower bounds is *added* to `|t|`, never needed, and the `t²` in the numerator is
dominated by `|t|²` alone. -/
theorem exists_bound_pole_correction_near {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) :
    ∃ δ > 0, ∃ C : ℝ, ∀ r : ℝ, 1 / 2 ≤ r → r < 1 → ∀ t : ℝ, |t| ≤ δ →
      ‖(1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
        - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * (((r * (∫ x, x ∂μ)) : ℝ) : ℂ)
            * (t : ℂ) * Complex.I)⁻¹‖ ≤ C := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  obtain ⟨δ₁, hδ₁, K, hK, hq⟩ := exists_norm_one_sub_charFun_add_le hint
  obtain ⟨δ₂, hδ₂, hlow1⟩ := exists_le_norm_one_sub_smul_charFun hint hm
  set c₁ : ℝ := min 1 (m / 4) / 2 with hc₁def
  set c₂ : ℝ := min 1 (Real.pi * m) / 2 with hc₂def
  have hc₁ : 0 < c₁ := by
    rw [hc₁def]
    have h : 0 < min 1 (m / 4) := lt_min one_pos (by positivity)
    linarith
  have hc₂ : 0 < c₂ := by
    rw [hc₂def]
    have h : 0 < min 1 (Real.pi * m) := lt_min one_pos (by positivity)
    linarith
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨min δ₁ δ₂ / (2 * Real.pi), by positivity, 4 * Real.pi ^ 2 * K / (c₁ * c₂),
    fun r hr hr1 t ht => ?_⟩
  have hr0 : (0 : ℝ) ≤ r := by linarith
  set u : ℝ := -(2 * Real.pi * t) with hu_def
  have habsu : |u| = 2 * Real.pi * |t| := by
    rw [hu_def, abs_neg, abs_mul, abs_of_pos h2π]
  have hu : |u| ≤ min δ₁ δ₂ := by
    rw [habsu]
    calc 2 * Real.pi * |t| ≤ 2 * Real.pi * (min δ₁ δ₂ / (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_left ht h2π.le
      _ = min δ₁ δ₂ := by field_simp
  have hu1 : |u| ≤ δ₁ := le_trans hu (min_le_left _ _)
  have hu2 : |u| ≤ δ₂ := le_trans hu (min_le_right _ _)
  set d₁ : ℂ := 1 - (r : ℂ) * charFun μ u with hd₁def
  set d₂ : ℂ := ((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I
    with hd₂def
  have hn1 : c₁ * ((1 - r) + |t|) ≤ ‖d₁‖ := by
    have habs : |t| ≤ |u| := by
      rw [habsu]; nlinarith [abs_nonneg t, Real.pi_gt_three]
    have hstep : c₁ * ((1 - r) + |t|) ≤ c₁ * ((1 - r) + |u|) :=
      mul_le_mul_of_nonneg_left (by linarith) hc₁.le
    exact le_trans hstep (hlow1 r hr hr1.le u hu2)
  have hn2 : c₂ * ((1 - r) + |t|) ≤ ‖d₂‖ := le_norm_model_denominator hm hr hr1.le t
  have hsum : 0 < (1 - r) + |t| := by
    have h0 : 0 < 1 - r := by linarith
    linarith [abs_nonneg t]
  have hd₁ne : d₁ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn1
    nlinarith
  have hd₂ne : d₂ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn2
    nlinarith
  have hdiff : d₂ - d₁ = -((r : ℂ) * (1 - charFun μ u + (m : ℂ) * (u : ℂ) * Complex.I)) := by
    rw [hd₁def, hd₂def, hu_def]
    push_cast
    ring
  have hnq : ‖d₂ - d₁‖ ≤ 4 * Real.pi ^ 2 * K * t ^ 2 := by
    rw [hdiff, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
    have h1 : ‖1 - charFun μ u + (m : ℂ) * (u : ℂ) * Complex.I‖ ≤ K * u ^ 2 := hq u hu1
    have h2 : u ^ 2 = 4 * Real.pi ^ 2 * t ^ 2 := by rw [hu_def]; ring
    calc r * ‖1 - charFun μ u + (m : ℂ) * (u : ℂ) * Complex.I‖
        ≤ 1 * (K * u ^ 2) := mul_le_mul hr1.le h1 (norm_nonneg _) zero_le_one
      _ = 4 * Real.pi ^ 2 * K * t ^ 2 := by rw [one_mul, h2]; ring
  have hprod : c₁ * c₂ * t ^ 2 ≤ ‖d₁ * d₂‖ := by
    rw [norm_mul]
    have hle : t ^ 2 ≤ ((1 - r) + |t|) ^ 2 := by
      calc t ^ 2 = |t| ^ 2 := (sq_abs t).symm
        _ ≤ ((1 - r) + |t|) ^ 2 := pow_le_pow_left₀ (abs_nonneg t) (by linarith) 2
    calc c₁ * c₂ * t ^ 2 ≤ c₁ * c₂ * ((1 - r) + |t|) ^ 2 :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (c₁ * ((1 - r) + |t|)) * (c₂ * ((1 - r) + |t|)) := by ring
      _ ≤ ‖d₁‖ * ‖d₂‖ := mul_le_mul hn1 hn2 (by positivity) (norm_nonneg _)
  have hprodpos : 0 < ‖d₁ * d₂‖ := by
    rw [norm_mul]
    have h1 : 0 < ‖d₁‖ := by rw [norm_pos_iff]; exact hd₁ne
    have h2 : 0 < ‖d₂‖ := by rw [norm_pos_iff]; exact hd₂ne
    positivity
  rw [inv_sub_inv hd₁ne hd₂ne, norm_div, div_le_iff₀ hprodpos]
  calc ‖d₂ - d₁‖ ≤ 4 * Real.pi ^ 2 * K * t ^ 2 := hnq
    _ = 4 * Real.pi ^ 2 * K / (c₁ * c₂) * (c₁ * c₂ * t ^ 2) := by field_simp
    _ ≤ 4 * Real.pi ^ 2 * K / (c₁ * c₂) * ‖d₁ * d₂‖ :=
        mul_le_mul_of_nonneg_left hprod (by positivity)

/-- **Uniform pole correction** (`lem:uniform-pole-correction`,
`eq:uniform-correction-bound`): for every band `[-T,T]` there are `r₀ < 1` and
`C < ∞` with

`‖(1 - rχ(-2πt))⁻¹ - ((1-r) + 2π i r m̂ t)⁻¹‖ ≤ C`,  `r₀ ≤ r < 1`, `|t| ≤ T`.

Two regimes. Near the origin this is `exists_bound_pole_correction_near`. On the
compact annulus `δ ≤ |t| ≤ T` neither denominator is small: nonlatticeness gives
`‖1 - χ(-2πt)‖ ≥ c` there (`exists_pos_le_norm_one_sub_charFun`), and
`1 - rχ = (1 - χ) + (1-r)χ` with `‖χ‖ ≤ 1` costs at most `1 - r ≤ c/2` once
`r ≥ 1 - c/2`; the model denominator is bounded below by `c₂δ` by
`le_norm_model_denominator`. So each term is bounded separately there — no
cancellation is needed away from the origin.

This is the last `μ`-dependent estimate of the Abel route; everything downstream
(the reference kernel, general bandlimited kernels, the local bound) uses it as a
black box together with the model-pole limit
`tendsto_integral_fourier_model_pole`. -/
theorem exists_bound_pole_correction_uniform {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) (T : ℝ) :
    ∃ r₀ : ℝ, 1 / 2 ≤ r₀ ∧ r₀ < 1 ∧ ∃ C : ℝ, ∀ r : ℝ, r₀ ≤ r → r < 1 → ∀ t : ℝ, |t| ≤ T →
      ‖(1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
        - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * (((r * (∫ x, x ∂μ)) : ℝ) : ℂ)
            * (t : ℂ) * Complex.I)⁻¹‖ ≤ C := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  obtain ⟨δ, hδ, C₁, hnear⟩ := exists_bound_pole_correction_near hint hm
  obtain ⟨c, hc, hann⟩ :=
    exists_pos_le_norm_one_sub_charFun hμ (show (0 : ℝ) < 2 * Real.pi * δ by positivity)
      (2 * Real.pi * T)
  set c₂ : ℝ := min 1 (Real.pi * m) / 2 with hc₂def
  have hc₂ : 0 < c₂ := by
    rw [hc₂def]
    have h : 0 < min 1 (Real.pi * m) := lt_min one_pos (by positivity)
    linarith
  have hcδ : (0 : ℝ) < c₂ * δ := by positivity
  refine ⟨max (1 / 2) (1 - c / 2), le_max_left _ _, max_lt (by norm_num) (by linarith),
    max C₁ (2 / c + 1 / (c₂ * δ)), fun r hr hr1 t ht => ?_⟩
  have hr12 : 1 / 2 ≤ r := le_trans (le_max_left _ _) hr
  by_cases hcase : |t| ≤ δ
  · exact le_trans (hnear r hr12 hr1 t hcase) (le_max_left _ _)
  · rw [not_le] at hcase
    have h1r : 1 - r ≤ c / 2 := by
      have h := le_trans (le_max_right _ _) hr
      linarith
    have h1r0 : (0 : ℝ) ≤ 1 - r := by linarith
    set u : ℝ := -(2 * Real.pi * t) with hu_def
    have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
    have habsu : |u| = 2 * Real.pi * |t| := by
      rw [hu_def, abs_neg, abs_mul, abs_of_pos h2π]
    have hcu : c ≤ ‖1 - charFun μ u‖ := by
      refine hann u ?_ ?_
      · rw [habsu]; exact mul_le_mul_of_nonneg_left ht h2π.le
      · rw [habsu]; exact mul_le_mul_of_nonneg_left hcase.le h2π.le
    set d₁ : ℂ := 1 - (r : ℂ) * charFun μ u with hd₁def
    set d₂ : ℂ := ((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I
      with hd₂def
    have hn1 : c / 2 ≤ ‖d₁‖ := by
      have hAB : (1 : ℂ) - charFun μ u = d₁ - ((1 - r : ℝ) : ℂ) * charFun μ u := by
        rw [hd₁def]; push_cast <;> ring
      have hnc : ‖((1 - r : ℝ) : ℂ) * charFun μ u‖ ≤ 1 - r := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h1r0]
        calc (1 - r) * ‖charFun μ u‖ ≤ (1 - r) * 1 :=
              mul_le_mul_of_nonneg_left (norm_charFun_le_one _) h1r0
          _ = 1 - r := mul_one _
      have h := norm_sub_le d₁ (((1 - r : ℝ) : ℂ) * charFun μ u)
      rw [← hAB] at h
      linarith
    have hn2 : c₂ * δ ≤ ‖d₂‖ := by
      have h := le_norm_model_denominator hm hr12 hr1.le t
      have hstep : c₂ * δ ≤ c₂ * ((1 - r) + |t|) :=
        mul_le_mul_of_nonneg_left (by linarith) hc₂.le
      exact le_trans hstep h
    have hb1 : ‖d₁⁻¹‖ ≤ 2 / c := by
      rw [norm_inv]
      have hval : (c / 2)⁻¹ = 2 / c := by field_simp
      rw [← hval]
      exact inv_anti₀ (by positivity) hn1
    have hb2 : ‖d₂⁻¹‖ ≤ 1 / (c₂ * δ) := by
      rw [norm_inv]
      have hval : (c₂ * δ)⁻¹ = 1 / (c₂ * δ) := by field_simp
      rw [← hval]
      exact inv_anti₀ hcδ hn2
    calc ‖d₁⁻¹ - d₂⁻¹‖ ≤ ‖d₁⁻¹‖ + ‖d₂⁻¹‖ := norm_sub_le _ _
      _ ≤ 2 / c + 1 / (c₂ * δ) := add_le_add hb1 hb2
      _ ≤ max C₁ (2 / c + 1 / (c₂ * δ)) := le_max_right _ _

/-- **The corrected resolvent converges pointwise off the origin**
(`eq:correction-pointwise-limit`): for `t ≠ 0`,

`D_r(t) ⟶ D₁(t) = (1 - χ(-2πt))⁻¹ - (2π i m̂ t)⁻¹`  as `r ↑ 1`.

Both `r = 1` denominators are nonzero — the first by nonlatticeness
(`charFun_ne_one_of_nonlattice`), the second because `m̂, t ≠ 0` — so this is just
continuity of `z ↦ z⁻¹` away from the origin, evaluated at `r = 1` and restricted
to the filter `𝓝[<] 1`. Together with the uniform bound
`exists_bound_pole_correction_uniform` this is what feeds dominated convergence in
`r` on the compact frequency band. -/
theorem tendsto_pole_correction {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : Nonlattice μ)
    (hm : 0 < ∫ x, x ∂μ) {t : ℝ} (ht : t ≠ 0) :
    Filter.Tendsto (fun r : ℝ => (1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
        - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * (((r * (∫ x, x ∂μ)) : ℝ) : ℂ)
            * (t : ℂ) * Complex.I)⁻¹)
      (nhdsWithin 1 (Set.Iio 1))
      (nhds ((1 - charFun μ (-(2 * Real.pi * t)))⁻¹
        - (2 * (Real.pi : ℂ) * ((∫ x, x ∂μ : ℝ) : ℂ) * (t : ℂ) * Complex.I)⁻¹)) := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  have htne : -(2 * Real.pi * t) ≠ 0 := by simp [Real.pi_ne_zero, ht]
  have hd1 : (1 : ℂ) - charFun μ (-(2 * Real.pi * t)) ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => charFun_ne_one_of_nonlattice hμ htne h.symm
  have hd2 : 2 * (Real.pi : ℂ) * (m : ℂ) * (t : ℂ) * Complex.I ≠ 0 := by
    have h1 : (Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    have h2 : (m : ℂ) ≠ 0 := by simpa using hm.ne'
    have h3 : (t : ℂ) ≠ 0 := by simpa using ht
    simp [h1, h2, h3, Complex.I_ne_zero]
  have hcont : ContinuousAt (fun r : ℝ => (1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
      - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
          * (t : ℂ) * Complex.I)⁻¹) 1 := by
    refine ContinuousAt.sub (ContinuousAt.inv₀ (by fun_prop) ?_)
      (ContinuousAt.inv₀ (by fun_prop) ?_)
    · simpa using hd1
    · push_cast
      simpa using hd2
  have h0 := hcont.tendsto
  have hval : (1 - ((1 : ℝ) : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
      - ((((1 : ℝ) - (1 : ℝ) : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * (((1 : ℝ) * m : ℝ) : ℂ)
          * (t : ℂ) * Complex.I)⁻¹
      = (1 - charFun μ (-(2 * Real.pi * t)))⁻¹
        - (2 * (Real.pi : ℂ) * (m : ℂ) * (t : ℂ) * Complex.I)⁻¹ := by
    push_cast
    norm_num
  rw [hval] at h0
  exact h0.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))

/-!
### Splitting the discounted resolvent

At *fixed* `r < 1` both denominators are bounded below by `1 - r` **everywhere** —
`‖1 - rχ‖ ≥ 1 - ‖rχ‖ ≥ 1 - r` and `‖(1-r) + 2π i r m̂ t‖ ≥ Re = 1 - r` — with no
hypothesis on `μ` and no appeal to the delicate small-`t` estimates. That crude
bound is all that is needed to make each of the three integrands below `L¹`
(dominated by `(1-r)⁻¹‖𝓕w‖`) and continuous, hence to split

`∫ 𝓕w e^{2πiyt}(1 - rχ(-2πt))⁻¹ dt = ∫ 𝓕w e^{2πiyt}D_r dt + M_r(y)`.

The uniform-in-`r` estimates of A-4g-4b are *not* used here; they are needed only
when `r ↑ 1`, where these bounds degenerate. -/

/-- `‖1 - rχ(u)‖ ≥ 1 - r`, for every frequency: the discounted denominator cannot
degenerate at fixed `r < 1`, because `‖χ‖ ≤ 1`. -/
theorem le_norm_one_sub_smul_charFun (μ : Measure ℝ) [IsProbabilityMeasure μ] {r : ℝ}
    (hr0 : 0 ≤ r) (u : ℝ) : 1 - r ≤ ‖1 - (r : ℂ) * charFun μ u‖ := by
  have h1 : ‖(r : ℂ) * charFun μ u‖ ≤ r := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
    calc r * ‖charFun μ u‖ ≤ r * 1 := mul_le_mul_of_nonneg_left (norm_charFun_le_one _) hr0
      _ = r := mul_one r
  have h2 := norm_sub_norm_le (1 : ℂ) ((r : ℂ) * charFun μ u)
  simp only [norm_one] at h2
  linarith

/-- `‖(1-r) + 2π i r m̂ t‖ ≥ 1 - r`, for every frequency: the real part *is*
`1 - r`. -/
theorem le_norm_model_denominator_re {m : ℝ} (r : ℝ) (t : ℝ) :
    1 - r ≤ ‖((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ)
      * Complex.I‖ := by
  set z : ℂ := ((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I
    with hz
  have hre : z.re = 1 - r := by simp [hz]
  rw [← hre]
  exact Complex.re_le_norm _

/-- The discounted Parseval integrand is `L¹` at fixed `r < 1`, dominated by
`(1-r)⁻¹‖𝓕w‖`. -/
theorem integrable_fourier_mul_discounted_resolvent {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {w : ℝ → ℂ} (hw : Integrable w) (hFw : Integrable (𝓕 w)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (y : ℝ) :
    Integrable (fun t : ℝ => 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
      * (1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹) := by
  have hFwc : Continuous (𝓕 w) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hw
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hne : ∀ t : ℝ, (1 : ℂ) - (r : ℂ) * charFun μ (-(2 * Real.pi * t)) ≠ 0 := by
    intro t h
    have hb := le_norm_one_sub_smul_charFun μ hr0 (-(2 * Real.pi * t))
    rw [h, norm_zero] at hb
    linarith
  have hexp : ∀ t : ℝ, ‖Complex.exp ((2 : ℂ) * Real.pi * t * y * Complex.I)‖ = 1 := by
    intro t
    have hcast : ((2 : ℂ) * Real.pi * t * y * Complex.I)
        = ((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I := by push_cast <;> ring
    rw [hcast, Complex.norm_exp_ofReal_mul_I]
  refine (hFw.norm.const_mul ((1 - r)⁻¹)).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · refine ((hFwc.mul (Complex.continuous_exp.comp (by fun_prop))).mul ?_).aestronglyMeasurable
    exact (continuous_const.sub (continuous_const.mul
      (continuous_charFun.comp (by fun_prop)))).inv₀ hne
  · rw [norm_mul, norm_mul, hexp t, mul_one, norm_inv]
    have hb : (‖(1 : ℂ) - (r : ℂ) * charFun μ (-(2 * Real.pi * t))‖)⁻¹ ≤ (1 - r)⁻¹ :=
      inv_anti₀ h1r (le_norm_one_sub_smul_charFun μ hr0 _)
    calc ‖𝓕 w t‖ * (‖(1 : ℂ) - (r : ℂ) * charFun μ (-(2 * Real.pi * t))‖)⁻¹
        ≤ ‖𝓕 w t‖ * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = (1 - r)⁻¹ * ‖𝓕 w t‖ := by ring

/-- The model-pole integrand is `L¹` at fixed `r < 1`, by the same domination.
No hypothesis on `μ` — indeed `μ` does not appear. -/
theorem integrable_fourier_mul_model_pole {w : ℝ → ℂ} (hw : Integrable w)
    (hFw : Integrable (𝓕 w)) {r : ℝ} (hr1 : r < 1) (m y : ℝ) :
    Integrable (fun t : ℝ => 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
      * (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I)⁻¹) := by
  have hFwc : Continuous (𝓕 w) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hw
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hne : ∀ t : ℝ, ((1 - r : ℝ) : ℂ)
      + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I ≠ 0 := by
    intro t h
    have hb := le_norm_model_denominator_re (m := m) r t
    rw [h, norm_zero] at hb
    linarith
  have hexp : ∀ t : ℝ, ‖Complex.exp ((2 : ℂ) * Real.pi * t * y * Complex.I)‖ = 1 := by
    intro t
    have hcast : ((2 : ℂ) * Real.pi * t * y * Complex.I)
        = ((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I := by push_cast <;> ring
    rw [hcast, Complex.norm_exp_ofReal_mul_I]
  refine (hFw.norm.const_mul ((1 - r)⁻¹)).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · refine ((hFwc.mul (Complex.continuous_exp.comp (by fun_prop))).mul ?_).aestronglyMeasurable
    exact (by fun_prop : Continuous fun t : ℝ => ((1 - r : ℝ) : ℂ)
      + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I).inv₀ hne
  · rw [norm_mul, norm_mul, hexp t, mul_one, norm_inv]
    have hb : (‖((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
        * (t : ℂ) * Complex.I‖)⁻¹ ≤ (1 - r)⁻¹ :=
      inv_anti₀ h1r (le_norm_model_denominator_re r t)
    calc ‖𝓕 w t‖ * (‖((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
          * (t : ℂ) * Complex.I‖)⁻¹
        ≤ ‖𝓕 w t‖ * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = (1 - r)⁻¹ * ‖𝓕 w t‖ := by ring

/-- **The discounted resolvent integral splits** as corrected part plus model
pole: for `0 ≤ r < 1`,

`∫ 𝓕w e^{2πiyt}(1 - rχ(-2πt))⁻¹ = ∫ 𝓕w e^{2πiyt}D_r + ∫ 𝓕w e^{2πiyt}((1-r)+2πi r m̂ t)⁻¹`.

Pointwise this is `sub_add_cancel`; the content is the two integrability side
conditions above, which `integral_sub` consumes. The second term is evaluated in
closed form by `integral_fourier_model_pole_Iio`, and its `r ↑ 1` limit is
`tendsto_integral_fourier_model_pole`; the first term is what
`exists_bound_pole_correction_uniform` and `tendsto_pole_correction` control. -/
theorem integral_fourier_discounted_resolvent_eq_add {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {w : ℝ → ℂ} (hw : Integrable w) (hFw : Integrable (𝓕 w)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (m y : ℝ) :
    ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * (1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
      = (∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * ((1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
            - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
                * (t : ℂ) * Complex.I)⁻¹))
        + ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
            * (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
                * (t : ℂ) * Complex.I)⁻¹ := by
  have hA := integrable_fourier_mul_discounted_resolvent (μ := μ) hw hFw hr0 hr1 y
  have hB := integrable_fourier_mul_model_pole hw hFw hr1 m y
  have hpt : ∀ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
      * ((1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
        - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I)⁻¹)
      = 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * (1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
        - 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
              * (t : ℂ) * Complex.I)⁻¹ := by
    intro t; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sub hA hB]
  ring

/-- The corrected integrand is `L¹` at fixed `r < 1`: the difference of the two
integrable pieces, re-associated. -/
theorem integrable_fourier_mul_pole_correction {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {w : ℝ → ℂ} (hw : Integrable w) (hFw : Integrable (𝓕 w)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (m y : ℝ) :
    Integrable (fun t : ℝ => 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
      * ((1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
        - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
            * (t : ℂ) * Complex.I)⁻¹)) := by
  have hA := integrable_fourier_mul_discounted_resolvent (μ := μ) hw hFw hr0 hr1 y
  have hB := integrable_fourier_mul_model_pole hw hFw hr1 m y
  refine (hA.sub hB).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.sub_apply]
  ring

/-- **The corrected term passes to the limit `r ↑ 1`** for a bandlimited kernel:

`∫ 𝓕w e^{2πiyt}D_r(t) dt ⟶ ∫ 𝓕w e^{2πiyt}D₁(t) dt`.

Dominated convergence along `𝓝[<] 1`, with the two A-4g-4b/4d2 ingredients in
their intended roles: the **constant** dominator `|C|‖𝓕w‖` comes from the uniform
bound on the band `|t| ≤ T` (and the integrand vanishes off the band, where the
uniform bound says nothing), and the pointwise limit comes from
`tendsto_pole_correction`, valid off the single point `t = 0` — a null set, which
is all dominated convergence needs.

This is where bandlimitedness of `w` is genuinely used: without compact support of
`𝓕w` there is no band on which to apply the uniform bound. -/
theorem tendsto_integral_fourier_pole_correction {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {w : ℝ → ℂ} {T : ℝ} (hw : Integrable w) (hFw : Integrable (𝓕 w))
    (hT : ∀ t : ℝ, T < |t| → 𝓕 w t = 0) (y : ℝ) :
    Filter.Tendsto (fun r : ℝ => ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * ((1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
          - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * (((r * (∫ x, x ∂μ)) : ℝ) : ℂ)
              * (t : ℂ) * Complex.I)⁻¹))
      (nhdsWithin 1 (Set.Iio 1))
      (nhds (∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * ((1 - charFun μ (-(2 * Real.pi * t)))⁻¹
          - (2 * (Real.pi : ℂ) * ((∫ x, x ∂μ : ℝ) : ℂ) * (t : ℂ) * Complex.I)⁻¹))) := by
  obtain ⟨r₀, hr₀half, hr₀one, C, hC⟩ := exists_bound_pole_correction_uniform hμ hint hm T
  have hev0 : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), r₀ ≤ r :=
    ((eventually_gt_nhds hr₀one).filter_mono nhdsWithin_le_nhds).mono fun r hr => hr.le
  have hev1 : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), r < 1 := eventually_mem_nhdsWithin
  have hevpos : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), 0 ≤ r :=
    ((eventually_gt_nhds (by linarith : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds).mono
      fun r hr => hr.le
  refine tendsto_integral_filter_of_dominated_convergence (fun t => |C| * ‖𝓕 w t‖) ?_ ?_
    (hFw.norm.const_mul _) ?_
  · filter_upwards [hevpos, hev1] with r hr0 hr1
    exact (integrable_fourier_mul_pole_correction (μ := μ) hw hFw hr0 hr1 _ y).1
  · filter_upwards [hev0, hev1] with r hr hr1
    refine Filter.Eventually.of_forall fun t => ?_
    by_cases hband : |t| ≤ T
    · have hb := hC r hr hr1 t hband
      have hexp : ‖Complex.exp ((2 : ℂ) * Real.pi * t * y * Complex.I)‖ = 1 := by
        have hcast : ((2 : ℂ) * Real.pi * t * y * Complex.I)
            = ((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I := by push_cast <;> ring
        rw [hcast, Complex.norm_exp_ofReal_mul_I]
      rw [norm_mul, norm_mul, hexp, mul_one]
      calc ‖𝓕 w t‖ * ‖(1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
            - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * (((r * (∫ x, x ∂μ)) : ℝ) : ℂ)
                * (t : ℂ) * Complex.I)⁻¹‖
          ≤ ‖𝓕 w t‖ * |C| :=
            mul_le_mul_of_nonneg_left (hb.trans (le_abs_self C)) (norm_nonneg _)
        _ = |C| * ‖𝓕 w t‖ := by ring
    · rw [not_le] at hband
      rw [hT t hband]
      simp
  · have h0 : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff]
    filter_upwards [h0] with t ht
    exact (tendsto_pole_correction hμ hm ht).const_mul _

/-!
### Abel's limit theorem for nonnegative series

The last step of the reference-kernel argument reads the *undiscounted* renewal
series off the discounted ones. For a **nonnegative** sequence this is elementary
and needs no Tauberian input: if `∑ₙ rⁿaₙ → L` as `r ↑ 1` then `a` is summable
with `∑ₙ aₙ = L`. One inequality compares each *finite* partial sum
`∑_{n<N} rⁿaₙ ≤ ∑ₙ rⁿaₙ` and lets `r ↑ 1` (the left side is a polynomial in `r`,
so continuous), giving `∑_{n<N} aₙ ≤ L` for every `N` and hence summability; the
other compares termwise `rⁿaₙ ≤ aₙ`.

Nonnegativity is exactly what the sinc-squared reference kernel supplies, and it
is why the plan insists on a nonnegative kernel here. Nothing in this subsection
is measure-theoretic; it is stated for a bare sequence.
-/

/-- **Abel's limit theorem for a nonnegative series.** If the discounted sums
`∑ₙ rⁿaₙ` converge to `L` as `r ↑ 1`, then `a` is summable and `∑ₙ aₙ = L`.

The summability hypothesis on each discounted series is genuinely needed: `a` may
grow, and summability of `∑ rⁿaₙ` for `r < 1` is what the renewal application
supplies (via the Chernoff bound / discounted Parseval), not something automatic. -/
theorem summable_and_tsum_eq_of_tendsto_tsum_pow_mul {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hsum : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable fun n => r ^ n * a n)
    {L : ℝ} (hL : Filter.Tendsto (fun r : ℝ => ∑' n, r ^ n * a n)
      (nhdsWithin 1 (Set.Iio 1)) (nhds L)) :
    Summable a ∧ ∑' n, a n = L := by
  have hpos : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), 0 ≤ r :=
    ((eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds).mono
      fun r hr => hr.le
  have hlt : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), r < 1 := eventually_mem_nhdsWithin
  have hpartial : ∀ N : ℕ, ∑ n ∈ Finset.range N, a n ≤ L := by
    intro N
    have h1 : Filter.Tendsto (fun r : ℝ => ∑ n ∈ Finset.range N, r ^ n * a n)
        (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds (∑ n ∈ Finset.range N, a n)) := by
      have hc : Continuous fun r : ℝ => ∑ n ∈ Finset.range N, r ^ n * a n := by fun_prop
      have h2 := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
      simpa using h2
    refine le_of_tendsto_of_tendsto h1 hL ?_
    filter_upwards [hpos, hlt] with r hr0 hr1
    exact (hsum r hr0 hr1).sum_le_tsum _ (fun i _ => mul_nonneg (pow_nonneg hr0 i) (ha i))
  have hsa : Summable a := summable_of_sum_range_le ha hpartial
  refine ⟨hsa, le_antisymm (hsa.tsum_le_of_sum_range_le hpartial) ?_⟩
  refine le_of_tendsto hL ?_
  filter_upwards [hpos, hlt] with r hr0 hr1
  refine (hsum r hr0 hr1).tsum_le_tsum (fun n => ?_) hsa
  calc r ^ n * a n ≤ 1 * a n :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hr0 hr1.le) (ha n)
    _ = a n := one_mul _

/-!
### The real bridge for a nonnegative kernel

Discounted Parseval is stated for `ℂ`-valued kernels, but Abel's limit theorem
above needs a *real nonnegative* sequence. For a real kernel `v ≥ 0` the two
descriptions differ only by `integral_ofReal` (which is unconditional, being the
`ℝ`-linear isometry `ofReal` commuted past a Bochner integral), so the discounted
smoothed renewal series is literally `ofReal` of a nonnegative real series.

Boundedness `v ≤ B` is assumed rather than derived. It gives both integrability of
`z ↦ v(y-z)` against each convolution power (a probability measure) and the
geometric domination `rⁿ∫v(y−z)dμ^{*n} ≤ B rⁿ` that makes each discounted series
summable — the hypothesis Abel's theorem needs and which is *not* automatic. For
the sinc-squared reference kernel it comes free from `sincSq_le`.
-/

/-- Each discounted smoothed renewal series is summable, for a bounded nonnegative
kernel: the terms are squeezed between `0` and `B rⁿ`. -/
theorem summable_pow_mul_integral_comp_sub {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {v : ℝ → ℝ} {B : ℝ} (hv0 : ∀ x, 0 ≤ v x) (hB : ∀ x, v x ≤ B) (hvc : Continuous v)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (y : ℝ) :
    Summable fun n => r ^ n * ∫ z, v (y - z) ∂(convPow μ n) := by
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun z : ℝ => v (y - z)) (convPow μ n) := fun n =>
    (hvc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hint : ∀ n : ℕ, Integrable (fun z : ℝ => v (y - z)) (convPow μ n) := by
    intro n
    refine (integrable_const B).mono' (hmeas n) (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (hv0 _)]
    exact hB _
  have hle : ∀ n : ℕ, ∫ z, v (y - z) ∂(convPow μ n) ≤ B := by
    intro n
    have h1 := integral_mono (hint n) (integrable_const B) (fun z => hB (y - z))
    simpa using h1
  have hnn : ∀ n : ℕ, 0 ≤ ∫ z, v (y - z) ∂(convPow μ n) := fun n =>
    integral_nonneg fun z => hv0 _
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg hr0 n) (hnn n)) (fun n => ?_)
    ((summable_geometric_of_lt_one hr0 hr1).mul_left B)
  calc r ^ n * ∫ z, v (y - z) ∂(convPow μ n) ≤ r ^ n * B :=
        mul_le_mul_of_nonneg_left (hle n) (pow_nonneg hr0 n)
    _ = B * r ^ n := by ring

/-- **Discounted Parseval for a real nonnegative kernel**: the discounted smoothed
renewal series is `ofReal` of a real series, and equals the resolvent integral.

This is the interface Abel's limit theorem consumes: the left-hand side is
`ofReal` of `∑ₙ rⁿaₙ` with `aₙ = ∫v(y−z)dμ^{*n} ≥ 0`, and the right-hand side is
what `integral_fourier_discounted_resolvent_eq_add`, A-4g-4d3 and
`tendsto_integral_fourier_model_pole` evaluate in the limit `r ↑ 1`. -/
theorem ofReal_tsum_pow_mul_integral_comp_sub_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {v : ℝ → ℝ} {B : ℝ} (hv0 : ∀ x, 0 ≤ v x) (hB : ∀ x, v x ≤ B) (hvc : Continuous v)
    (hvi : Integrable v) (hFv : Integrable (𝓕 fun x => ((v x : ℝ) : ℂ)))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (y : ℝ) :
    ((∑' n, r ^ n * ∫ z, v (y - z) ∂(convPow μ n) : ℝ) : ℂ)
      = ∫ t : ℝ, 𝓕 (fun x => ((v x : ℝ) : ℂ)) t
          * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * (1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹ := by
  have hwc : Continuous (fun x => ((v x : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hvc
  have hwi : Integrable (fun x => ((v x : ℝ) : ℂ)) := hvi.ofReal
  have hsummable := summable_pow_mul_integral_comp_sub (μ := μ) hv0 hB hvc hr0 hr1 y
  have hpartial : ∀ N : ℕ,
      ∑ n ∈ Finset.range N, (r : ℂ) ^ n * ∫ z, ((v (y - z) : ℝ) : ℂ) ∂(convPow μ n)
      = ((∑ n ∈ Finset.range N, r ^ n * ∫ z, v (y - z) ∂(convPow μ n) : ℝ) : ℂ) := by
    intro N
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    exact integral_ofReal
  have h1 := tendsto_sum_pow_integral_comp_sub (μ := μ) hwc hwi hFv hr0 hr1 y
  rw [funext hpartial] at h1
  have h2 : Filter.Tendsto
      (fun N : ℕ => ((∑ n ∈ Finset.range N, r ^ n * ∫ z, v (y - z) ∂(convPow μ n) : ℝ) : ℂ))
      Filter.atTop
      (nhds ((∑' n, r ^ n * ∫ z, v (y - z) ∂(convPow μ n) : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hsummable.hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique h2 h1

/-- **The undiscounted smoothed renewal series, evaluated** (the `r ↑ 1` half of
`prop:reference-kernel`). For a bounded nonnegative continuous bandlimited kernel
`v`, the series `∑ₙ ∫v(y−z)dμ^{*n}` converges, with

`∑ₙ ∫v(y−z)dμ^{*n} = Re ∫ 𝓕v(t)e^{2πiyt}D₁(t) dt + (∫_{-∞}^y v)/m̂`.

All the Abel machinery meets here: the discounted series is `ofReal` of a
nonnegative real series (A-4g-4d4b), it splits as corrected part plus model pole
(A-4g-4d1), the two pieces converge as `r ↑ 1` (A-4g-4d3 and
`tendsto_integral_fourier_model_pole`), and Abel's theorem (A-4g-4d4a) transfers
the limit to the undiscounted series. Real parts are taken at the very end, which
is legitimate without knowing a priori that the complex limit is real: `Re` is
continuous and `Re ∘ ofReal = id`.

`y` is still fixed. Letting `y → ∞` — where Riemann–Lebesgue kills the first term
and `∫_{-∞}^y v → ∫v`, leaving `(∫v)/m̂` — is the next unit and must not be
interchanged with the `r ↑ 1` limit taken here. -/
theorem summable_integral_comp_sub_and_tsum_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {v : ℝ → ℝ} {B T : ℝ} (hv0 : ∀ x, 0 ≤ v x) (hB : ∀ x, v x ≤ B) (hvc : Continuous v)
    (hvi : Integrable v) (hFv : Integrable (𝓕 fun x => ((v x : ℝ) : ℂ)))
    (hT : ∀ t : ℝ, T < |t| → 𝓕 (fun x => ((v x : ℝ) : ℂ)) t = 0) (y : ℝ) :
    Summable (fun n => ∫ z, v (y - z) ∂(convPow μ n)) ∧
      ∑' n, ∫ z, v (y - z) ∂(convPow μ n)
        = (∫ t : ℝ, 𝓕 (fun x => ((v x : ℝ) : ℂ)) t
            * Complex.exp (2 * Real.pi * t * y * Complex.I)
            * ((1 - charFun μ (-(2 * Real.pi * t)))⁻¹
              - (2 * (Real.pi : ℂ) * ((∫ x, x ∂μ : ℝ) : ℂ) * (t : ℂ) * Complex.I)⁻¹)).re
          + (∫ x in Set.Iio y, v x) / (∫ x, x ∂μ) := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  set w : ℝ → ℂ := fun x => ((v x : ℝ) : ℂ) with hwdef
  have hwc : Continuous w := Complex.continuous_ofReal.comp hvc
  have hwi : Integrable w := hvi.ofReal
  have hpos : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), 0 ≤ r :=
    ((eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds).mono
      fun r hr => hr.le
  have hlt : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), r < 1 := eventually_mem_nhdsWithin
  have hlimC := (tendsto_integral_fourier_pole_correction hμ hint hm hwi hFv hT y).add
    (tendsto_integral_fourier_model_pole hwc hwi hFv hm y)
  have heq : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)),
      ((∑' n, r ^ n * ∫ z, v (y - z) ∂(convPow μ n) : ℝ) : ℂ)
        = (∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
            * ((1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
              - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
                  * (t : ℂ) * Complex.I)⁻¹))
          + ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
              * (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
                  * (t : ℂ) * Complex.I)⁻¹ := by
    filter_upwards [hpos, hlt] with r hr0 hr1
    rw [ofReal_tsum_pow_mul_integral_comp_sub_eq hv0 hB hvc hvi hFv hr0 hr1 y,
      integral_fourier_discounted_resolvent_eq_add hwi hFv hr0 hr1 m y]
  have hlim : Filter.Tendsto
      (fun r : ℝ => ((∑' n, r ^ n * ∫ z, v (y - z) ∂(convPow μ n) : ℝ) : ℂ))
      (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds _) := (Filter.tendsto_congr' heq).mpr hlimC
  have hlimR : Filter.Tendsto (fun r : ℝ => ∑' n, r ^ n * ∫ z, v (y - z) ∂(convPow μ n))
      (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds _) :=
    ((Complex.continuous_re.tendsto _).comp hlim).congr fun r => by simp
  obtain ⟨hs, hval⟩ := summable_and_tsum_eq_of_tendsto_tsum_pow_mul
    (fun n => integral_nonneg fun z => hv0 _)
    (fun r hr0 hr1 => summable_pow_mul_integral_comp_sub (μ := μ) hv0 hB hvc hr0 hr1 y)
    hlimR
  refine ⟨hs, ?_⟩
  rw [hval]
  have hIio : (∫ x in Set.Iio y, w x) = ((∫ x in Set.Iio y, v x : ℝ) : ℂ) := integral_ofReal
  rw [Complex.add_re, hIio]
  congr 1
  simp
  ring

/-!
### The reference-kernel limit: the constant `1/m̂`

Letting `y → ∞` in `summable_integral_comp_sub_and_tsum_eq` finishes A-4g-4. The
corrected term is the Fourier transform of `t ↦ 𝓕v(t)D₁(t)` evaluated at `−y`, so
Riemann–Lebesgue sends it to `0`; the mass term `∫_{-∞}^y v` increases to `∫v`.
What is left is exactly `(∫v)/m̂`.
-/

/-- **Riemann–Lebesgue in this file's exponential convention**: for *any* `g`,

`∫ g(t)e^{2πity} dt ⟶ 0`  as `|y| → ∞`.

Generalizes `tendsto_integral_fourier_resolvent` away from the specific resolvent
integrand. Unconditional, because `Real.zero_at_infty_fourier` is: a
non-integrable integrand gives the junk value `0` at every frequency. -/
theorem tendsto_integral_mul_exp_cocompact (g : ℝ → ℂ) :
    Filter.Tendsto (fun y : ℝ => ∫ t : ℝ, g t * Complex.exp (2 * Real.pi * t * y * Complex.I))
      (Filter.cocompact ℝ) (nhds 0) := by
  have hrw : ∀ y : ℝ, (∫ t : ℝ, g t * Complex.exp (2 * Real.pi * t * y * Complex.I))
      = 𝓕 g (-y) := by
    intro y
    rw [Real.fourier_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Real.inner_apply, smul_eq_mul]
    have hce : Complex.exp (((-2 * Real.pi * (t * -y) : ℝ) : ℂ) * Complex.I)
        = Complex.exp (2 * Real.pi * t * y * Complex.I) := by
      congr 1; push_cast <;> ring
    rw [hce]; ring
  have hneg : Filter.Tendsto (fun y : ℝ => -y) (Filter.cocompact ℝ) (Filter.cocompact ℝ) := by
    rw [cocompact_eq_atBot_atTop]
    exact Filter.tendsto_sup.2 ⟨Filter.tendsto_neg_atBot_atTop.mono_right le_sup_right,
      Filter.tendsto_neg_atTop_atBot.mono_right le_sup_left⟩
  simp only [hrw]
  exact (Real.zero_at_infty_fourier _).comp hneg

/-- **The reference-kernel renewal limit** (`prop:reference-kernel`; the
replacement for the old A-4g-4, and the step at which Blackwell's constant is
finally identified):

`∑ₙ ∫ v(y−z) μ^{*n}(dz) ⟶ (∫v)/m̂`  as `y → ∞`,

for every bounded nonnegative continuous bandlimited kernel `v`. Note this is
already more general than the note's proposition, which is stated for the
sinc-squared kernel: nothing beyond `v ≥ 0`, `v ≤ B`, continuity, `v, 𝓕v ∈ L¹` and
compact support of `𝓕v` is used.

The limit order is the one fixed in the proof note: `r ↑ 1` at fixed `y` happens
inside `summable_integral_comp_sub_and_tsum_eq`, and only here is `y → ∞` taken.
Interchanging them would produce `1/(2m̂)`. -/
theorem tendsto_tsum_integral_comp_sub {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {v : ℝ → ℝ} {B T : ℝ} (hv0 : ∀ x, 0 ≤ v x) (hB : ∀ x, v x ≤ B) (hvc : Continuous v)
    (hvi : Integrable v) (hFv : Integrable (𝓕 fun x => ((v x : ℝ) : ℂ)))
    (hT : ∀ t : ℝ, T < |t| → 𝓕 (fun x => ((v x : ℝ) : ℂ)) t = 0) :
    Filter.Tendsto (fun y : ℝ => ∑' n, ∫ z, v (y - z) ∂(convPow μ n)) Filter.atTop
      (nhds ((∫ x, v x) / (∫ x, x ∂μ))) := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  set w : ℝ → ℂ := fun x => ((v x : ℝ) : ℂ) with hwdef
  set D : ℝ → ℂ := fun t => (1 - charFun μ (-(2 * Real.pi * t)))⁻¹
    - (2 * (Real.pi : ℂ) * (m : ℂ) * (t : ℂ) * Complex.I)⁻¹ with hD
  have hRL : Filter.Tendsto (fun y : ℝ => (∫ t : ℝ, 𝓕 w t
      * Complex.exp (2 * Real.pi * t * y * Complex.I) * D t).re) Filter.atTop (nhds 0) := by
    have hshape : ∀ y : ℝ, (∫ t : ℝ, 𝓕 w t
        * Complex.exp (2 * Real.pi * t * y * Complex.I) * D t)
        = ∫ t : ℝ, (𝓕 w t * D t) * Complex.exp (2 * Real.pi * t * y * Complex.I) := by
      intro y
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      ring
    have h1 : Filter.Tendsto (fun y : ℝ => ∫ t : ℝ, 𝓕 w t
        * Complex.exp (2 * Real.pi * t * y * Complex.I) * D t) Filter.atTop (nhds 0) := by
      simp only [hshape]
      exact (tendsto_integral_mul_exp_cocompact (fun t => 𝓕 w t * D t)).mono_left
        (by rw [cocompact_eq_atBot_atTop]; exact le_sup_right)
    have h2 := (Complex.continuous_re.tendsto _).comp h1
    simp only [Complex.zero_re] at h2
    exact h2
  have hmass : Filter.Tendsto (fun y : ℝ => (∫ x in Set.Iio y, v x) / m) Filter.atTop
      (nhds ((∫ x, v x) / m)) := by
    have h := (aecover_Iio (l := Filter.atTop) (b := id)
      Filter.tendsto_id).integral_tendsto_of_countably_generated hvi
    exact h.div_const m
  have hsum := hRL.add hmass
  rw [zero_add] at hsum
  refine hsum.congr fun y => ?_
  exact ((summable_integral_comp_sub_and_tsum_eq hμ hint hm hv0 hB hvc hvi hFv hT y).2).symm

/-!
### Boundedness from an integrable transform

The signed case (A-4g-4e) subtracts a multiple of the reference kernel from the
target kernel, and to split the renewal series along that subtraction one needs
each smoothed integral to exist separately. Both kernels are bounded, so both are
integrable against every convolution power — and boundedness is not an extra
hypothesis: a continuous `w` with `w, 𝓕w ∈ L¹` is automatically bounded by
`‖𝓕w‖_{L¹}`, being the inverse transform of an `L¹` function.
-/

/-- A kernel with integrable Fourier transform is bounded by `‖𝓕w‖_{L¹}`.

Immediate from pointwise inversion (`eq_integral_fourier_mul_exp`) and
`‖e^{iθ}‖ = 1`. This is what makes the boundedness hypothesis of
`summable_pow_mul_integral_comp_sub` cheap to satisfy in practice. -/
theorem norm_le_integral_norm_fourier {w : ℝ → ℂ} (hwc : Continuous w) (hw : Integrable w)
    (hFw : Integrable (𝓕 w)) (x : ℝ) : ‖w x‖ ≤ ∫ t : ℝ, ‖𝓕 w t‖ := by
  have hexp : ∀ t : ℝ, ‖Complex.exp ((2 : ℂ) * Real.pi * t * x * Complex.I)‖ = 1 := by
    intro t
    have hcast : ((2 : ℂ) * Real.pi * t * x * Complex.I)
        = ((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I := by push_cast <;> ring
    rw [hcast, Complex.norm_exp_ofReal_mul_I]
  calc ‖w x‖ = ‖∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * x * Complex.I)‖ := by
        rw [eq_integral_fourier_mul_exp hwc hw hFw x]
    _ ≤ ∫ t : ℝ, ‖𝓕 w t * Complex.exp (2 * Real.pi * t * x * Complex.I)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ t : ℝ, ‖𝓕 w t‖ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        beta_reduce
        rw [norm_mul, hexp t, mul_one]

/-- A bounded continuous kernel is integrable against any finite measure after the
reflection-translation `z ↦ w(y − z)`. -/
theorem integrable_comp_sub_of_bounded {ν : Measure ℝ} [IsFiniteMeasure ν] {w : ℝ → ℂ} {B : ℝ}
    (hwc : Continuous w) (hB : ∀ x, ‖w x‖ ≤ B) (y : ℝ) :
    Integrable (fun z : ℝ => w (y - z)) ν := by
  refine (integrable_const B).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact (hwc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact hB _

/-!
### Fourier linearity for kernel corrections

A-4g-4e replaces a signed kernel `w` by the difference `w − cκ` with
`c = (∫w)/(∫κ)`, so that the corrected kernel has total mass zero. Verifying that
its transform vanishes at the origin needs two elementary facts about `𝓕` that
Mathlib states only in the general `VectorFourier` form.

**API note.** `𝓕` is notation for `Real.fourierIntegral`, which is *definitionally*
but not *syntactically* `VectorFourier.fourierIntegral 𝐞 volume (innerₛₗ ℝ)`. So
`rw [VectorFourier.fourierIntegral_add …]` fails against a goal written with `𝓕`;
the lemma has to be instantiated into a `have` with an explicit `𝓕`-typed
statement (which elaborates up to defeq) and rewritten from there.
-/

/-- `𝓕 (c · f) = c · 𝓕 f`. No integrability hypothesis: both sides are the junk
value `0` when the integrand fails to be integrable. -/
theorem fourier_const_mul (c : ℂ) (f : ℝ → ℂ) (t : ℝ) :
    𝓕 (fun x => c * f x) t = c * 𝓕 f t := by
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [Real.inner_apply, smul_eq_mul]
  ring

/-- `𝓕 f 0 = ∫ f`: the transform at the origin is the total mass. This is what
turns the normalization `c = (∫w)/(∫κ)` into the vanishing `𝓕(w − cκ)(0) = 0`. -/
theorem fourier_zero_eq_integral (f : ℝ → ℂ) : 𝓕 f 0 = ∫ x : ℝ, f x := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp

/-- `𝓕 (f − c·g) = 𝓕 f − c·𝓕 g`, the exact shape the kernel correction needs. -/
theorem fourier_sub_const_mul {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (c : ℂ)
    (t : ℝ) : 𝓕 (fun x => f x - c * g x) t = 𝓕 f t - c * 𝓕 g t := by
  have hrw : (fun x => f x - c * g x) = f + fun x => (-c) * g x := by
    funext x
    simp only [Pi.add_apply, neg_mul]
    ring
  have hadd : 𝓕 (f + fun x => (-c) * g x) = 𝓕 f + 𝓕 (fun x => (-c) * g x) :=
    VectorFourier.fourierIntegral_add Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf
      (hg.const_mul (-c))
  rw [hrw, congrFun hadd t]
  simp only [Pi.add_apply]
  rw [fourier_const_mul]
  ring

/-- **The mass-corrected kernel is a difference kernel.** For `c = (∫w)/(∫κ)`, the
kernel `w − cκ` has a bandlimited transform vanishing to first order at the origin:

* `𝓕(w − cκ)` is supported in `[-max(T_w,T_κ), max(T_w,T_κ)]`;
* `‖𝓕(w − cκ)(t)‖ ≤ (L_w + ‖c‖L_κ)|t|`.

These are exactly the two hypotheses of
`tendsto_zero_of_tendsto_sum_integral_comp_sub`, so the corrected kernel's renewal
series tends to `0` and the whole limit for `w` comes from the reference kernel
`κ` — which is `tendsto_tsum_integral_comp_sub`. The normalization is what makes
`𝓕(w − cκ)(0) = ∫w − c∫κ = 0`, using `fourier_zero_eq_integral`.

The Lipschitz-at-the-origin hypotheses are assumed rather than derived. They do not
follow from bandlimitedness plus integrability: for the sinc-squared reference
kernel `x·κ(x) ∉ L¹`, so `𝓕κ` cannot be differentiated under the integral sign —
one instead reads the bound off the explicit piecewise-linear formula for `𝓕κ`. -/
theorem fourier_sub_ref_kernel {w κ : ℝ → ℂ} {Tw Tκ Lw Lκ : ℝ}
    (hwi : Integrable w) (hκi : Integrable κ)
    (hwT : ∀ t : ℝ, Tw < |t| → 𝓕 w t = 0) (hκT : ∀ t : ℝ, Tκ < |t| → 𝓕 κ t = 0)
    (hwL : ∀ t : ℝ, ‖𝓕 w t - 𝓕 w 0‖ ≤ Lw * |t|)
    (hκL : ∀ t : ℝ, ‖𝓕 κ t - 𝓕 κ 0‖ ≤ Lκ * |t|)
    (hκ0 : (∫ x : ℝ, κ x) ≠ 0) :
    (∀ t : ℝ, max Tw Tκ < |t| →
        𝓕 (fun x => w x - ((∫ x : ℝ, w x) / (∫ x : ℝ, κ x)) * κ x) t = 0)
      ∧ (∀ t : ℝ, ‖𝓕 (fun x => w x - ((∫ x : ℝ, w x) / (∫ x : ℝ, κ x)) * κ x) t‖
          ≤ (Lw + ‖(∫ x : ℝ, w x) / (∫ x : ℝ, κ x)‖ * Lκ) * |t|) := by
  set c : ℂ := (∫ x : ℝ, w x) / (∫ x : ℝ, κ x) with hc
  have hsplit : ∀ t : ℝ, 𝓕 (fun x => w x - c * κ x) t = 𝓕 w t - c * 𝓕 κ t :=
    fun t => fourier_sub_const_mul hwi hκi c t
  have hzero : 𝓕 (fun x => w x - c * κ x) 0 = 0 := by
    rw [hsplit 0, fourier_zero_eq_integral, fourier_zero_eq_integral, hc]
    field_simp
    ring
  refine ⟨fun t ht => ?_, fun t => ?_⟩
  · rw [hsplit t, hwT t (lt_of_le_of_lt (le_max_left _ _) ht),
      hκT t (lt_of_le_of_lt (le_max_right _ _) ht)]
    ring
  · have hrw : 𝓕 (fun x => w x - c * κ x) t
        = (𝓕 w t - 𝓕 w 0) - c * (𝓕 κ t - 𝓕 κ 0) := by
      have h0 := hzero
      rw [hsplit 0] at h0
      rw [hsplit t]
      linear_combination h0
    rw [hrw]
    calc ‖(𝓕 w t - 𝓕 w 0) - c * (𝓕 κ t - 𝓕 κ 0)‖
        ≤ ‖𝓕 w t - 𝓕 w 0‖ + ‖c * (𝓕 κ t - 𝓕 κ 0)‖ := norm_sub_le _ _
      _ = ‖𝓕 w t - 𝓕 w 0‖ + ‖c‖ * ‖𝓕 κ t - 𝓕 κ 0‖ := by rw [norm_mul]
      _ ≤ Lw * |t| + ‖c‖ * (Lκ * |t|) := by
          gcongr
          · exact hwL t
          · exact hκL t
      _ = (Lw + ‖c‖ * Lκ) * |t| := by ring

/-- The smoothed renewal series of the corrected kernel `w − cκ` converges, with
limit `S y − c·(κ-series at y)`.

Termwise `∫(w − cκ')(y−z)dμ^{*n} = ∫w(y−z)dμ^{*n} − c∫κ'(y−z)dμ^{*n}`, which needs
both smoothed integrals to exist separately — that is what
`integrable_comp_sub_of_bounded` provides, with the bound for `w` coming from
`norm_le_integral_norm_fourier`. -/
theorem tendsto_sum_integral_comp_sub_sub {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {w : ℝ → ℂ} {κ : ℝ → ℝ} {Bw Bκ : ℝ} (hwc : Continuous w) (hwB : ∀ x, ‖w x‖ ≤ Bw)
    (hκc : Continuous κ) (hκB : ∀ x, ‖((κ x : ℝ) : ℂ)‖ ≤ Bκ)
    (c : ℂ) (y : ℝ) {Sy : ℂ}
    (hS : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, ∫ z, w (y - z) ∂(convPow μ n))
      Filter.atTop (nhds Sy))
    (hsum : Summable fun n => ∫ z, κ (y - z) ∂(convPow μ n)) :
    Filter.Tendsto (fun N => ∑ n ∈ Finset.range N,
        ∫ z, (w (y - z) - c * ((κ (y - z) : ℝ) : ℂ)) ∂(convPow μ n))
      Filter.atTop
      (nhds (Sy - c * ((∑' n, ∫ z, κ (y - z) ∂(convPow μ n) : ℝ) : ℂ))) := by
  have hκ'c : Continuous (fun x : ℝ => ((κ x : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hκc
  have hterm : ∀ n : ℕ, ∫ z, (w (y - z) - c * ((κ (y - z) : ℝ) : ℂ)) ∂(convPow μ n)
      = (∫ z, w (y - z) ∂(convPow μ n))
        - c * ((∫ z, κ (y - z) ∂(convPow μ n) : ℝ) : ℂ) := by
    intro n
    have h1 : Integrable (fun z : ℝ => w (y - z)) (convPow μ n) :=
      integrable_comp_sub_of_bounded hwc hwB y
    have h2 : Integrable (fun z : ℝ => ((κ (y - z) : ℝ) : ℂ)) (convPow μ n) :=
      integrable_comp_sub_of_bounded hκ'c hκB y
    rw [integral_sub h1 (h2.const_mul c), integral_const_mul]
    congr 2
    exact integral_ofReal
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N,
      ∫ z, (w (y - z) - c * ((κ (y - z) : ℝ) : ℂ)) ∂(convPow μ n)
      = (∑ n ∈ Finset.range N, ∫ z, w (y - z) ∂(convPow μ n))
        - c * ((∑ n ∈ Finset.range N, ∫ z, κ (y - z) ∂(convPow μ n) : ℝ) : ℂ) := by
    intro N
    rw [Finset.sum_congr rfl (fun n _ => hterm n), Finset.sum_sub_distrib, ← Finset.mul_sum]
    congr 2
    push_cast
    rfl
  simp only [hpart]
  refine hS.sub (Filter.Tendsto.const_mul c ?_)
  exact (Complex.continuous_ofReal.tendsto _).comp hsum.hasSum.tendsto_sum_nat

/-- **The renewal limit for a general (possibly signed) bandlimited kernel**
(`thm:band-limited`): if the smoothed renewal series of `w` converges pointwise to
`S`, then

`S y ⟶ (∫w)/m̂`  as `y → ∞`.

Decompose `w = (w − cκ) + cκ` with `c = (∫w)/(∫κ)`. The corrected kernel is a
difference kernel (`fourier_sub_ref_kernel`), so its series tends to `0` by
`tendsto_zero_of_tendsto_sum_integral_comp_sub`; the reference kernel contributes
`(∫κ)/m̂` by `tendsto_tsum_integral_comp_sub`; and `c·(∫κ)/m̂ = (∫w)/m̂`.

The reference kernel is taken **abstractly**, not as the sinc-squared kernel. That
is forced: this module is a pure-Mathlib leaf and does not import
`AbsorptionCutoff.Supercritical.RenewalKernel`, so no concrete witness is nameable here.
Discharging these hypotheses at `sincSq` belongs in a corollary downstream; the
Lipschitz-at-the-origin one is read off `𝓕κ = triangle(−·)`, giving `Lκ = 1`. -/
theorem tendsto_of_tendsto_sum_integral_comp_sub_bandlimited {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {κ : ℝ → ℝ} {Bκ Tκ Lκ : ℝ} (hκ0 : ∀ x, 0 ≤ κ x) (hκB : ∀ x, κ x ≤ Bκ)
    (hκc : Continuous κ) (hκi : Integrable κ)
    (hFκ : Integrable (𝓕 fun x => ((κ x : ℝ) : ℂ)))
    (hκT : ∀ t : ℝ, Tκ < |t| → 𝓕 (fun x => ((κ x : ℝ) : ℂ)) t = 0)
    (hκL : ∀ t : ℝ, ‖𝓕 (fun x => ((κ x : ℝ) : ℂ)) t
        - 𝓕 (fun x => ((κ x : ℝ) : ℂ)) 0‖ ≤ Lκ * |t|)
    (hLκ0 : 0 ≤ Lκ) (hκpos : 0 < ∫ x, κ x)
    {w : ℝ → ℂ} {Tw Lw : ℝ} (hwc : Continuous w) (hwi : Integrable w)
    (hFw : Integrable (𝓕 w)) (hwT : ∀ t : ℝ, Tw < |t| → 𝓕 w t = 0)
    (hwL : ∀ t : ℝ, ‖𝓕 w t - 𝓕 w 0‖ ≤ Lw * |t|) (hLw0 : 0 ≤ Lw)
    {S : ℝ → ℂ}
    (hS : ∀ y : ℝ, Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, ∫ z, w (y - z) ∂(convPow μ n))
      Filter.atTop (nhds (S y))) :
    Filter.Tendsto S Filter.atTop (nhds ((∫ x, w x) / ((∫ x, x ∂μ : ℝ) : ℂ))) := by
  have hκ'c : Continuous (fun x : ℝ => ((κ x : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hκc
  have hκ'i : Integrable (fun x : ℝ => ((κ x : ℝ) : ℂ)) := hκi.ofReal
  have hIκ : (∫ x : ℝ, ((κ x : ℝ) : ℂ)) = ((∫ x : ℝ, κ x : ℝ) : ℂ) := integral_ofReal
  have hIκ0 : (∫ x : ℝ, ((κ x : ℝ) : ℂ)) ≠ 0 := by
    rw [hIκ]
    simpa using hκpos.ne'
  obtain ⟨hvT, hvL⟩ := fourier_sub_ref_kernel (Tw := Tw) (Tκ := Tκ) (Lw := Lw) (Lκ := Lκ)
    hwi hκ'i hwT hκT hwL hκL hIκ0
  set c : ℂ := (∫ x : ℝ, w x) / (∫ x : ℝ, ((κ x : ℝ) : ℂ)) with hcdef
  have hvc : Continuous (fun x : ℝ => w x - c * ((κ x : ℝ) : ℂ)) :=
    hwc.sub (continuous_const.mul hκ'c)
  have hvi : Integrable (fun x : ℝ => w x - c * ((κ x : ℝ) : ℂ)) := hwi.sub (hκ'i.const_mul c)
  have hFvi : Integrable (𝓕 fun x : ℝ => w x - c * ((κ x : ℝ) : ℂ)) := by
    refine (hFw.sub (hFκ.const_mul c)).congr (Filter.Eventually.of_forall fun t => ?_)
    rw [fourier_sub_const_mul hwi hκ'i c t]
    simp only [Pi.sub_apply]
  have hwB : ∀ x, ‖w x‖ ≤ ∫ t : ℝ, ‖𝓕 w t‖ := norm_le_integral_norm_fourier hwc hwi hFw
  have hκ'B : ∀ x, ‖((κ x : ℝ) : ℂ)‖ ≤ Bκ := by
    intro x
    rw [Complex.norm_real, Real.norm_of_nonneg (hκ0 x)]
    exact hκB x
  have hκsum : ∀ y : ℝ, Summable fun n => ∫ z, κ (y - z) ∂(convPow μ n) := fun y =>
    (summable_integral_comp_sub_and_tsum_eq hμ hint hm hκ0 hκB hκc hκi hFκ hκT y).1
  have hSvlim : ∀ y : ℝ, Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      ∫ z, (w (y - z) - c * ((κ (y - z) : ℝ) : ℂ)) ∂(convPow μ n)) Filter.atTop
      (nhds (S y - c * ((∑' n, ∫ z, κ (y - z) ∂(convPow μ n) : ℝ) : ℂ))) := fun y =>
    tendsto_sum_integral_comp_sub_sub hwc hwB hκc hκ'B c y (hS y) (hκsum y)
  have hzero := tendsto_zero_of_tendsto_sum_integral_comp_sub hμ hint hm hvc hvi hFvi
    (by positivity : (0 : ℝ) ≤ Lw + ‖c‖ * Lκ) hvT hvL hSvlim
  have hκser := tendsto_tsum_integral_comp_sub hμ hint hm hκ0 hκB hκc hκi hFκ hκT
  have hlim2 : Filter.Tendsto
      (fun y : ℝ => c * ((∑' n, ∫ z, κ (y - z) ∂(convPow μ n) : ℝ) : ℂ))
      Filter.atTop (nhds (c * (((∫ x : ℝ, κ x) / (∫ x : ℝ, x ∂μ) : ℝ) : ℂ))) :=
    ((Complex.continuous_ofReal.tendsto _).comp hκser).const_mul c
  have hfin := hzero.add hlim2
  rw [zero_add] at hfin
  have hval : c * (((∫ x : ℝ, κ x) / (∫ x : ℝ, x ∂μ) : ℝ) : ℂ)
      = (∫ x : ℝ, w x) / ((∫ x : ℝ, x ∂μ : ℝ) : ℂ) := by
    have hne : ((∫ x : ℝ, κ x : ℝ) : ℂ) ≠ 0 := by simpa using hκpos.ne'
    rw [hcdef, hIκ]
    push_cast
    field_simp
  rw [hval] at hfin
  refine hfin.congr fun y => ?_
  ring

end Renewal

end AbsorptionCutoff
end

section
-- module Solutions.OAIQ247_JB.Supercritical_RenewalKernel
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The smoothing kernel of the renewal mini-library

Split out of `AbsorptionCutoff.Supercritical.Renewal` purely for build time: these are
finished, computation-heavy proofs (`sincSq_le` and `triangle_eq` carry the
expensive `nlinarith`/interval work) that the in-progress Blackwell argument only
consumes, never edits. This module depends on nothing else in `AbsorptionCutoff`.

Blackwell's theorem is proved by testing the renewal measure against a kernel `w`
whose Fourier transform has **compact support** — that is what makes the
Riemann-Lebesgue step legitimate without any decay assumption on `charFun` at
infinity, which nonlatticeness alone does not provide.

The kernel is built from the unit box `1_{[-1,1]}`: its Fourier transform is the
sinc function, so the *square* of that transform is nonnegative and is itself the
Fourier transform of the triangle `1_{[-1,1]} * 1_{[-1,1]}`, supported in
`[-2,2]`. Mathlib has the convolution theorem (`fourier_mul_convolution_eq`) but
no Fourier transform of an indicator, so the closed forms are computed here.
-/

open MeasureTheory
open scoped Convolution FourierTransform

namespace AbsorptionCutoff

namespace Renewal

/-! ### Dilation

Mathlib has no dilation rule for `𝓕`, and the d.R.i. approximation argument needs
one: the approximate identity is a *rescaled* smoothing kernel, and the whole
point of rescaling is that the band `supp 𝓕` scales the other way. -/

/-- **The Fourier transform of a dilate**, `𝓕(f(a·))(ξ) = a⁻¹ 𝓕f(ξ/a)` for `a > 0`.

Concretely: compressing a kernel by `a` stretches the support of its transform by
`a`, which is what turns a fixed bandlimited kernel into a family of approximate
identities that stay bandlimited.

The proof is the change of variables `u = a v` under the Fourier integral. Because
`rw` cannot see through the beta-redex `∫ v, (fun u => …) (a * v)`,
`Measure.integral_comp_mul_left` is instantiated as a `have` first. -/
theorem fourier_comp_mul_left (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    𝓕 (fun t => f (a * t)) ξ = (a⁻¹ : ℝ) • 𝓕 f (ξ / a) := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  set g : ℝ → ℂ :=
    fun u => Complex.exp ((-2 * Real.pi * (inner ℝ u (ξ / a)) : ℝ) * Complex.I) • f u with hg
  rw [Real.fourier_eq', Real.fourier_eq']
  have h1 : ∀ v : ℝ,
      Complex.exp ((-2 * Real.pi * (inner ℝ v ξ) : ℝ) * Complex.I) • f (a * v) = g (a * v) := by
    intro v
    simp only [hg, RCLike.inner_apply, conj_trivial]
    congr 2
    push_cast
    field_simp
  have h2 := Measure.integral_comp_mul_left g a
  rw [integral_congr_ae (Filter.Eventually.of_forall h1), h2, abs_inv, abs_of_pos ha]

/-- The band of a dilate: if `𝓕f` vanishes outside `[-T,T]`, then `𝓕(f(a·))`
vanishes outside `[-aT, aT]`. -/
theorem fourier_comp_mul_left_eq_zero {f : ℝ → ℂ} {a T : ℝ} (ha : 0 < a)
    (hf : ∀ t : ℝ, T < |t| → 𝓕 f t = 0) {ξ : ℝ} (hξ : a * T < |ξ|) :
    𝓕 (fun t => f (a * t)) ξ = 0 := by
  rw [fourier_comp_mul_left f ha]
  have : T < |ξ / a| := by
    rw [abs_div, abs_of_pos ha, lt_div_iff₀ ha, mul_comm]
    exact hξ
  rw [hf _ this, smul_zero]

lemma integrable_unitBox : Integrable unitBox := by
  rw [unitBox]
  refine (integrable_indicator_iff measurableSet_Icc).2 ?_
  exact integrableOn_const (by simp) |>.mono_set (le_refl _)

/-- **The Fourier transform of the unit box is the sinc function**,
`𝓕 1_{[-1,1]}(t) = sin (2πt) / (πt)`.

In particular it is real-valued, so its square — the kernel used below — is
nonnegative. -/
theorem fourier_unitBox {t : ℝ} (ht : t ≠ 0) :
    𝓕 unitBox t = ((Real.sin (2 * Real.pi * t) / (Real.pi * t) : ℝ) : ℂ) := by
  have hstep : 𝓕 unitBox t
      = ∫ x in (-1 : ℝ)..1,
          Complex.exp ((((-2 * Real.pi * t : ℝ)) : ℂ) * Complex.I * x) := by
    rw [Real.fourier_eq']
    simp only [Real.inner_apply, unitBox]
    have hpt : ∀ v : ℝ,
        Complex.exp ((-2 * Real.pi * (v * t) : ℝ) * Complex.I) •
            Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ => (1 : ℂ)) v
          = Set.indicator (Set.Icc (-1 : ℝ) 1)
              (fun x : ℝ =>
                Complex.exp ((((-2 * Real.pi * t : ℝ)) : ℂ) * Complex.I * x)) v := by
      intro v
      by_cases hv : v ∈ Set.Icc (-1 : ℝ) 1
      · simp only [Set.indicator_of_mem hv, smul_eq_mul, mul_one]
        congr 1
        push_cast
        ring
      · simp [Set.indicator_of_notMem hv]
    simp only [hpt]
    rw [MeasureTheory.integral_indicator measurableSet_Icc,
      intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hc : (((-2 * Real.pi * t : ℝ)) : ℂ) * Complex.I ≠ 0 := by
    refine mul_ne_zero ?_ Complex.I_ne_zero
    simpa using ht
  rw [hstep, integral_exp_mul_complex hc]
  set z : ℂ := ((2 * Real.pi * t : ℝ) : ℂ) with hz
  have h2 : ((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I * ((1 : ℝ) : ℂ) = -z * Complex.I := by
    rw [hz]; push_cast <;> ring
  have h3 : ((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I * ((-1 : ℝ) : ℂ) = z * Complex.I := by
    rw [hz]; push_cast <;> ring
  rw [h2, h3]
  -- `e^{-izθ} - e^{izθ} = -2i sin θ`
  have hA : Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)
      = 2 * Complex.sin z * (-Complex.I) := by
    have h := Complex.two_sin z
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination Complex.I * h
      + (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * hI
  rw [hA, hz, ← Complex.ofReal_sin]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  push_cast
  field_simp

/-- The removable singularity of `fourier_unitBox` at the origin: the transform
takes the value `|[-1,1]| = 2` there. -/
theorem fourier_unitBox_zero : 𝓕 unitBox 0 = 2 := by
  rw [Real.fourier_eq', unitBox]
  simp only [Real.inner_apply, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul, mul_zero]
  rw [MeasureTheory.integral_indicator measurableSet_Icc]
  simp
  norm_num

open scoped Convolution

lemma integrable_triangle : Integrable triangle :=
  integrable_unitBox.integrable_convolution _ integrable_unitBox

/-- The convolution theorem for the triangle: `𝓕(1_{[-1,1]} ⋆ 1_{[-1,1]}) = (𝓕 1_{[-1,1]})²`. -/
lemma fourier_triangle (t : ℝ) : 𝓕 triangle t = (𝓕 unitBox t) ^ 2 := by
  rw [triangle, Real.fourier_mul_convolution_eq integrable_unitBox integrable_unitBox, sq]

lemma sincSq_nonneg (t : ℝ) : 0 ≤ sincSq t := by
  unfold sincSq; split <;> positivity

/-- The kernel is exactly the Fourier transform of the triangle. -/
lemma ofReal_sincSq (t : ℝ) : ((sincSq t : ℝ) : ℂ) = 𝓕 triangle t := by
  rw [fourier_triangle]
  unfold sincSq
  split
  · subst ‹t = 0›
    rw [fourier_unitBox_zero]
    norm_num
  · rw [fourier_unitBox ‹t ≠ 0›]
    push_cast
    ring

lemma continuous_fourier_triangle : Continuous (𝓕 triangle) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ integrable_triangle

lemma continuous_sincSq : Continuous sincSq := by
  have h : sincSq = fun t => (𝓕 triangle t).re := by
    funext t; rw [← ofReal_sincSq]; simp
  rw [h]
  exact Complex.continuous_re.comp continuous_fourier_triangle

lemma support_unitBox : Function.support unitBox = Set.Icc (-1 : ℝ) 1 := by
  rw [unitBox]
  ext x
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1 <;> simp [Function.mem_support, hx]

lemma support_triangle_subset : Function.support triangle ⊆ Set.Icc (-2 : ℝ) 2 := by
  refine (support_convolution_subset (ContinuousLinearMap.mul ℂ ℂ) (f := unitBox)
    (g := unitBox) (μ := volume)).trans ?_
  rw [support_unitBox, Set.Icc_add_Icc (by norm_num) (by norm_num)]
  norm_num

/-- The kernel is dominated by a multiple of the Cauchy density: `|sin| ≤ |·|`
near the origin gives the bound `4`, and `|sin| ≤ 1` gives `(πt)^{-2}` away from
it. This is what makes it integrable. -/
lemma sincSq_le (t : ℝ) : sincSq t ≤ 8 * (1 + t ^ 2)⁻¹ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi2 : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
  have hden : (0 : ℝ) < 1 + t ^ 2 := by positivity
  unfold sincSq
  split
  · subst ‹t = 0›
    norm_num
  · rename_i ht
    have ht2 : (0 : ℝ) < (Real.pi * t) ^ 2 := by positivity
    by_cases h : t ^ 2 ≤ 1
    · have h1 : (Real.sin (2 * Real.pi * t)) ^ 2 ≤ (2 * Real.pi * t) ^ 2 := by
        have := Real.abs_sin_le_abs (x := 2 * Real.pi * t)
        nlinarith [abs_nonneg (Real.sin (2 * Real.pi * t)), abs_nonneg (2 * Real.pi * t),
          sq_abs (Real.sin (2 * Real.pi * t)), sq_abs (2 * Real.pi * t)]
      have h2 : (Real.sin (2 * Real.pi * t) / (Real.pi * t)) ^ 2 ≤ 4 := by
        rw [div_pow, div_le_iff₀ ht2]
        nlinarith
      have h3 : (4 : ℝ) ≤ 8 * (1 + t ^ 2)⁻¹ := by
        rw [le_mul_inv_iff₀ hden]
        nlinarith
      linarith
    · have h' : 1 < t ^ 2 := by simpa using lt_of_not_ge h
      have h1 : (Real.sin (2 * Real.pi * t)) ^ 2 ≤ 1 := by
        have := Real.abs_sin_le_one (2 * Real.pi * t)
        nlinarith [sq_abs (Real.sin (2 * Real.pi * t)), abs_nonneg (Real.sin (2 * Real.pi * t))]
      have h2 : (Real.sin (2 * Real.pi * t) / (Real.pi * t)) ^ 2 ≤ ((Real.pi * t) ^ 2)⁻¹ := by
        rw [div_pow, div_eq_mul_inv]
        exact mul_le_of_le_one_left (by positivity) h1
      have h3 : ((Real.pi * t) ^ 2)⁻¹ ≤ 8 * (1 + t ^ 2)⁻¹ := by
        rw [inv_le_iff_one_le_mul₀ ht2]
        have hinv : (0 : ℝ) < (1 + t ^ 2)⁻¹ := inv_pos.mpr hden
        have hkey : (1 + t ^ 2) ≤ 8 * (Real.pi * t) ^ 2 := by
          have hpisq : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
          have hexp : (Real.pi * t) ^ 2 = Real.pi ^ 2 * t ^ 2 := by ring
          rw [hexp]
          nlinarith [sq_nonneg t]
        calc (1 : ℝ) = (1 + t ^ 2) * (1 + t ^ 2)⁻¹ := by field_simp
          _ ≤ (8 * (Real.pi * t) ^ 2) * (1 + t ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right hkey hinv.le
          _ = 8 * (1 + t ^ 2)⁻¹ * (Real.pi * t) ^ 2 := by ring
      linarith

lemma integrable_sincSq : Integrable sincSq := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul 8)
    continuous_sincSq.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (sincSq_nonneg t)]
  exact sincSq_le t

/-- Integrability of `𝓕 triangle`, the hypothesis Fourier inversion needs. -/
lemma integrable_fourier_triangle : Integrable (𝓕 triangle) := by
  have h : (𝓕 triangle) = fun t => ((sincSq t : ℝ) : ℂ) := by
    funext t; rw [ofReal_sincSq]
  rw [h]
  exact integrable_sincSq.ofReal

/-- **The triangle in closed form**: `(1_{[-1,1]} ⋆ 1_{[-1,1]})(x) = (2 - |x|)⁺`.

Needed because Fourier inversion is applied *at* the triangle, and its hypothesis
is continuity there. Mathlib's continuity lemmas for convolutions
(`HasCompactSupport.continuous_convolution_left/right`,
`BddAbove.continuous_convolution_right_of_integrable`) all require one factor to
be *continuous*, which the box is not — so the closed form is computed instead.
The integrand is the indicator of `[-1,1] ∩ [x-1,x+1] = [max(-1,x-1), min(1,x+1)]`,
whose length is `2 - |x|` when positive. -/
theorem triangle_eq (x : ℝ) : triangle x = ((max (2 - |x|) 0 : ℝ) : ℂ) := by
  have hpt : ∀ t : ℝ, (ContinuousLinearMap.mul ℂ ℂ) (unitBox t) (unitBox (x - t))
      = Set.indicator (Set.Icc (max (-1) (x - 1)) (min 1 (x + 1))) (fun _ => (1 : ℂ)) t := by
    intro t
    by_cases h : t ∈ Set.Icc (max (-1 : ℝ) (x - 1)) (min 1 (x + 1))
    · have hmem := h
      simp only [Set.mem_Icc, max_le_iff, le_min_iff] at h
      have h1 : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨h.1.1, h.2.1⟩
      have h2 : x - t ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [h.2.2], by linarith [h.1.2]⟩
      rw [Set.indicator_of_mem hmem]
      simp [unitBox, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
    · rw [Set.indicator_of_notMem h]
      by_cases h1 : t ∈ Set.Icc (-1 : ℝ) 1
      · by_cases h2 : x - t ∈ Set.Icc (-1 : ℝ) 1
        · simp only [Set.mem_Icc] at h1 h2
          exact absurd (⟨by simp only [max_le_iff]; constructor <;> linarith [h1.1, h2.2],
            by simp only [le_min_iff]; constructor <;> linarith [h1.2, h2.1]⟩ :
              t ∈ Set.Icc (max (-1 : ℝ) (x - 1)) (min 1 (x + 1))) h
        · simp [unitBox, Set.indicator_of_notMem h2]
      · simp [unitBox, Set.indicator_of_notMem h1]
  rw [triangle, convolution]
  simp only [hpt]
  rw [MeasureTheory.integral_indicator measurableSet_Icc, MeasureTheory.setIntegral_const,
    Real.volume_real_Icc, Complex.real_smul, mul_one]
  congr 2
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, min_eq_left (by linarith), max_eq_right (by linarith)]
    ring
  · rw [abs_of_nonpos hx, min_eq_right (by linarith), max_eq_left (by linarith)]
    ring

lemma continuous_triangle : Continuous triangle := by
  have h : triangle = fun x => ((max (2 - |x|) 0 : ℝ) : ℂ) := funext triangle_eq
  rw [h]
  fun_prop

/-- **The Fourier transform of the kernel is the reflected triangle**, hence
compactly supported (`support_triangle_subset`). This is the property that makes
the Riemann–Lebesgue step of Blackwell's theorem work: the `t`-integral in the
Parseval atom `integral_comp_sub_eq_integral_charFun` runs over a compact set,
where `1 - charFun μ` is bounded away from `0` off the origin
(`charFun_ne_one_of_nonlattice` plus continuity). -/
theorem fourier_fourier_triangle (x : ℝ) : 𝓕 (𝓕 triangle) x = triangle (-x) := by
  have h : 𝓕⁻ (𝓕 triangle) (-x) = triangle (-x) :=
    integrable_triangle.fourierInv_fourier_eq integrable_fourier_triangle
      continuous_triangle.continuousAt
  rw [Real.fourierInv_eq_fourier_neg] at h
  simpa using h

/-- The same statement with the kernel written as the real-valued `sincSq`, the
form `integral_comp_sub_eq_integral_charFun` consumes. -/
theorem fourier_ofReal_sincSq (x : ℝ) :
    𝓕 (fun t : ℝ => ((sincSq t : ℝ) : ℂ)) x = triangle (-x) := by
  have h : (fun t : ℝ => ((sincSq t : ℝ) : ℂ)) = 𝓕 triangle := by
    funext t; rw [ofReal_sincSq]
  rw [h, fourier_fourier_triangle]

/-- The kernel is bounded below on a neighbourhood of the origin — all that the
domination step `A-4e` needs, and cheaper than any explicit sinc inequality:
it follows from continuity and `sincSq 0 = 4`. -/
lemma exists_pos_le_sincSq : ∃ δ > 0, ∀ t ∈ Set.Icc (-δ) δ, 2 ≤ sincSq t := by
  have h : ∀ᶠ t in nhds (0 : ℝ), 2 < sincSq t := by
    refine continuous_sincSq.continuousAt.eventually_const_lt ?_
    rw [sincSq_zero]; norm_num
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hε, hball⟩ := h
  refine ⟨ε / 2, by linarith, fun t ht => ?_⟩
  have hd : dist t 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_lt]
    constructor <;> [linarith [ht.1]; linarith [ht.2]]
  exact (hball hd).le

end Renewal

end AbsorptionCutoff
end

section
-- module Solutions.OAIQ247_JB.Supercritical_RenewalSinc
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The renewal limit at the sinc-squared kernel

`AbsorptionCutoff.Supercritical.RenewalAbel` proves the renewal limit for an *abstract*
reference kernel, because it is a pure-Mathlib leaf and cannot name a concrete
witness. This module is the meeting point: it imports the kernel constructions of
`AbsorptionCutoff.Supercritical.RenewalKernel` and discharges every abstract hypothesis at
`Renewal.sincSq`.

## Main results

* `Renewal.integral_sincSq`: `∫ sincSq = 2`, read off `𝓕(sincSq) = triangle(−·)`
  at the origin.
* `Renewal.tendsto_tsum_integral_comp_sub_sincSq`: `∑ₙ ∫ sincSq(y−z) μ^{*n}(dz) ⟶ 2/m̂`.
* `Renewal.tendsto_of_tendsto_sum_integral_comp_sub_sincSq`: the same limit for a
  general bandlimited kernel, with `sincSq` supplying the reference kernel.
* `Renewal.exists_bound_renewalMeasure_Icc_of_expTransform`: the two-sided uniform
  cell bound `U([y, y+ℓ]) ≤ C` for *all* `y`, combining the `atTop` bound above
  with the Chernoff left-tail bound of `AbsorptionCutoff.Supercritical.Renewal`.

The bandlimited-approximation machinery built on top of these — the rescaled
approximate identity and the smoothing `w ⋆ K_a` — lives in the continuation
module `AbsorptionCutoff.Supercritical.RenewalApprox`.
-/

open MeasureTheory
open scoped Convolution ENNReal NNReal FourierTransform

namespace AbsorptionCutoff

namespace Renewal

/-! ### Discharging the abstract reference-kernel hypotheses at `sincSq` -/

/-- The kernel is bounded by `8`. Coarser than `sincSq_le`, and all the renewal
argument needs: boundedness is used only to dominate `rⁿ∫sincSq(y−z)dμ^{*n}` by
`8rⁿ`. -/
lemma sincSq_le_eight (t : ℝ) : sincSq t ≤ 8 := by
  have h1 : sincSq t ≤ 8 * (1 + t ^ 2)⁻¹ := sincSq_le t
  have h2 : (1 + t ^ 2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    nlinarith [sq_nonneg t]
  calc sincSq t ≤ 8 * (1 + t ^ 2)⁻¹ := h1
    _ ≤ 8 * 1 := by gcongr
    _ = 8 := by ring

/-- `𝓕(sincSq)` is integrable: it *is* the reflected triangle, which is
integrable. -/
lemma integrable_fourier_ofReal_sincSq :
    Integrable (𝓕 fun t : ℝ => ((sincSq t : ℝ) : ℂ)) := by
  have h : (𝓕 fun t : ℝ => ((sincSq t : ℝ) : ℂ)) = fun x : ℝ => triangle (-x) :=
    funext fourier_ofReal_sincSq
  rw [h]
  exact integrable_triangle.comp_neg

/-- `𝓕(sincSq)` is supported in `[-2,2]`: bandlimitedness of the reference
kernel, from `support_triangle_subset`. -/
lemma fourier_ofReal_sincSq_eq_zero {t : ℝ} (ht : 2 < |t|) :
    𝓕 (fun x : ℝ => ((sincSq x : ℝ) : ℂ)) t = 0 := by
  rw [fourier_ofReal_sincSq]
  by_contra h
  have hmem : (-t) ∈ Function.support triangle := h
  have h2 := support_triangle_subset hmem
  rw [Set.mem_Icc] at h2
  have habs : |t| ≤ 2 := abs_le.2 ⟨by linarith [h2.2], by linarith [h2.1]⟩
  linarith

/-- **`∫ sincSq = 2`.** The transform at the origin is the total mass
(`fourier_zero_eq_integral`), and `𝓕(sincSq)(0) = triangle 0 = 2`. In particular
the reference kernel has *positive* mass, which is what makes the normalization
`c = (∫w)/(∫κ)` legitimate. -/
theorem integral_sincSq : ∫ x : ℝ, sincSq x = 2 := by
  have h1 : (∫ x : ℝ, ((sincSq x : ℝ) : ℂ)) = triangle 0 := by
    rw [← fourier_zero_eq_integral, fourier_ofReal_sincSq]
    norm_num
  rw [triangle_eq] at h1
  norm_num at h1
  have h2 : ((∫ x : ℝ, sincSq x : ℝ) : ℂ) = (2 : ℂ) := by
    rw [← h1]
    exact integral_ofReal.symm
  exact_mod_cast h2

lemma integral_sincSq_pos : 0 < ∫ x : ℝ, sincSq x := by
  rw [integral_sincSq]; norm_num

/-- The transform of the reference kernel is Lipschitz at the origin with constant
`1`: `‖𝓕κ(t) − 𝓕κ(0)‖ = |max(2−|t|,0) − 2| = min(|t|,2) ≤ |t|`.

This cannot be obtained by differentiating under the integral sign — `x·sincSq(x)`
is not integrable, since `sincSq ≍ (1+x²)⁻¹` — so it is read off the explicit
piecewise-linear formula `triangle_eq` instead. -/
lemma norm_fourier_ofReal_sincSq_sub_le (t : ℝ) :
    ‖𝓕 (fun x : ℝ => ((sincSq x : ℝ) : ℂ)) t
      - 𝓕 (fun x : ℝ => ((sincSq x : ℝ) : ℂ)) 0‖ ≤ 1 * |t| := by
  rw [fourier_ofReal_sincSq, fourier_ofReal_sincSq, triangle_eq, triangle_eq]
  have h0 : max (2 - |(-0 : ℝ)|) 0 = 2 := by norm_num
  rw [h0, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, one_mul, abs_neg]
  rcases le_total (2 - |t|) 0 with h | h
  · rw [max_eq_right h]
    rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [max_eq_left h]
    rw [abs_of_nonpos (by linarith [abs_nonneg t])]
    linarith

/-! ### The concrete renewal limits -/

/-- **The reference-kernel renewal limit at `sincSq`**:
`∑ₙ ∫ sincSq(y−z) μ^{*n}(dz) ⟶ 2/m̂` as `y → ∞`. -/
theorem tendsto_tsum_integral_comp_sub_sincSq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) :
    Filter.Tendsto (fun y : ℝ => ∑' n, ∫ z, sincSq (y - z) ∂(convPow μ n)) Filter.atTop
      (nhds (2 / (∫ x, x ∂μ))) := by
  have h := tendsto_tsum_integral_comp_sub (B := 8) (T := 2) hμ hint hm sincSq_nonneg
    sincSq_le_eight continuous_sincSq integrable_sincSq integrable_fourier_ofReal_sincSq
    (fun _ ht => fourier_ofReal_sincSq_eq_zero ht)
  rwa [integral_sincSq] at h

/-- The smoothed renewal series at `sincSq` is summable at every `y`. -/
lemma summable_integral_comp_sub_sincSq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) (y : ℝ) :
    Summable fun n => ∫ z, sincSq (y - z) ∂(convPow μ n) :=
  (summable_integral_comp_sub_and_tsum_eq (B := 8) (T := 2) hμ hint hm sincSq_nonneg
    sincSq_le_eight continuous_sincSq integrable_sincSq integrable_fourier_ofReal_sincSq
    (fun _ ht => fourier_ofReal_sincSq_eq_zero ht) y).1

/-- **The uniform local renewal bound, on a fixed short interval** (A-4e): there
are `δ > 0` and `C < ∞` with

`U([y−δ, y+δ]) ≤ C`  for all large `y`.

Two ingredients meet: `renewalMeasure_le_ofReal_tsum_integral` turns the lower
bound `2 ≤ sincSq` on `[-δ,δ]` into `U([y−δ,y+δ]) ≤ (smoothed series)/2`, and
`tendsto_tsum_integral_comp_sub_sincSq` says the smoothed series converges, hence
is eventually bounded.

**The bound is stated on `atTop`, not for all `y ∈ ℝ`, and that is not an
artefact.** A limit at `+∞` says nothing about the left tail, and under these
hypotheses — nonlattice, `MemLp id 2 μ`, positive drift — nothing bounds `U` near
`−∞`. Getting a genuinely global bound would need a finite exponential moment
(A-2's Chernoff estimate `renewalMeasure_lt_top_of_expTransform_lt_one`), which the
chapter's *tilted* law has but a general nonlattice law does not; it would
therefore have to be added to the hypotheses. The `atTop` form is what a directly
Riemann integrable tail estimate needs. -/
theorem exists_bound_renewalMeasure_Icc_atTop {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) :
    ∃ δ > 0, ∃ C : ℝ, ∀ᶠ y : ℝ in Filter.atTop,
      renewalMeasure μ (Set.Icc (y - δ) (y + δ)) ≤ ENNReal.ofReal C := by
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_sincSq
  refine ⟨δ, hδ, (2 / (∫ x, x ∂μ) + 1) / 2, ?_⟩
  have hev : ∀ᶠ y : ℝ in Filter.atTop,
      (∑' n, ∫ z, sincSq (y - z) ∂(convPow μ n)) ≤ 2 / (∫ x, x ∂μ) + 1 :=
    (tendsto_tsum_integral_comp_sub_sincSq hμ hint hm).eventually_le_const (by linarith)
  filter_upwards [hev] with y hy
  calc renewalMeasure μ (Set.Icc (y - δ) (y + δ))
      ≤ ENNReal.ofReal ((∑' n, ∫ z, sincSq (y - z) ∂(convPow μ n)) / 2) := by
        refine renewalMeasure_le_ofReal_tsum_integral sincSq_nonneg continuous_sincSq
          sincSq_le_eight measurableSet_Icc two_pos (fun z hz => ?_)
          (summable_integral_comp_sub_sincSq hμ hint hm y)
        refine hδle _ ?_
        rw [Set.mem_Icc] at hz ⊢
        constructor <;> linarith [hz.1, hz.2]
    _ ≤ ENNReal.ofReal ((2 / (∫ x, x ∂μ) + 1) / 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        linarith

/-- **The uniform local renewal bound at any fixed length** (A-4e): for every
`ℓ`, there is `C < ∞` with `U([y, y+ℓ]) ≤ C` for all large `y`.

The short interval of `exists_bound_renewalMeasure_Icc_atTop` has a length `2δ`
fixed by the kernel, so intervals of a prescribed length are covered by finitely
many translates and the bounds added. The cover is built by induction on the number
of cells using `Set.Icc_union_Icc_eq_Icc`, which is cheaper than a floor-function
argument; each cell's bound is the short-interval bound translated along
`y ↦ y + (2kδ + δ)`, a map tending to `atTop`, so all the cells' bounds hold
eventually together.

Rescaling the kernel to cover `[y, y+ℓ]` in one step would instead require a
scaling lemma for the whole package — band, mass and boundedness all change — so
the finite cover is the cheaper route. As in the short-interval version, the bound
is on `atTop` only. -/
theorem exists_bound_renewalMeasure_Icc_atTop_of_length {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    (ℓ : ℝ) :
    ∃ C : ℝ, ∀ᶠ y : ℝ in Filter.atTop,
      renewalMeasure μ (Set.Icc y (y + ℓ)) ≤ ENNReal.ofReal C := by
  obtain ⟨δ, hδ, C₀, hC₀⟩ := exists_bound_renewalMeasure_Icc_atTop hμ hint hm
  set D : ℝ := max C₀ 0 with hDdef
  have hD0 : 0 ≤ D := le_max_right _ _
  have hCD : ∀ᶠ y : ℝ in Filter.atTop,
      renewalMeasure μ (Set.Icc (y - δ) (y + δ)) ≤ ENNReal.ofReal D := by
    filter_upwards [hC₀] with y hy
    exact hy.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  -- the bound on a union of `K` cells, by induction on `K`
  have key : ∀ K : ℕ, ∀ᶠ y : ℝ in Filter.atTop,
      renewalMeasure μ (Set.Icc y (y + 2 * (K : ℝ) * δ))
        ≤ ENNReal.ofReal (((K : ℝ) + 1) * D) := by
    intro K
    induction K with
    | zero =>
        filter_upwards [hCD] with y hy
        have hsub : Set.Icc y (y + 2 * ((0 : ℕ) : ℝ) * δ) ⊆ Set.Icc (y - δ) (y + δ) := by
          intro x hx
          rw [Set.mem_Icc] at hx ⊢
          norm_num at hx
          constructor <;> [linarith [hx.1]; linarith [hx.2]]
        refine (measure_mono hsub).trans (hy.trans (ENNReal.ofReal_le_ofReal ?_))
        push_cast
        linarith
    | succ K ih =>
        have hshift : ∀ᶠ y : ℝ in Filter.atTop,
            renewalMeasure μ (Set.Icc (y + 2 * (K : ℝ) * δ) (y + 2 * ((K : ℝ) + 1) * δ))
              ≤ ENNReal.ofReal D := by
          have h := (Filter.tendsto_atTop_add_const_right Filter.atTop
            (2 * (K : ℝ) * δ + δ) Filter.tendsto_id).eventually hCD
          filter_upwards [h] with y hy
          simp only [id_eq] at hy
          have he1 : y + (2 * (K : ℝ) * δ + δ) - δ = y + 2 * (K : ℝ) * δ := by ring
          have he2 : y + (2 * (K : ℝ) * δ + δ) + δ = y + 2 * ((K : ℝ) + 1) * δ := by ring
          rwa [he1, he2] at hy
        filter_upwards [ih, hshift] with y h1 h2
        have hsplit : Set.Icc y (y + 2 * ((K : ℕ) + 1 : ℝ) * δ)
            = Set.Icc y (y + 2 * (K : ℝ) * δ)
              ∪ Set.Icc (y + 2 * (K : ℝ) * δ) (y + 2 * ((K : ℝ) + 1) * δ) := by
          rw [Set.Icc_union_Icc_eq_Icc] <;> nlinarith [Nat.cast_nonneg (α := ℝ) K]
        have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast <;> ring
        rw [hcast, hsplit]
        calc renewalMeasure μ (Set.Icc y (y + 2 * (K : ℝ) * δ)
              ∪ Set.Icc (y + 2 * (K : ℝ) * δ) (y + 2 * ((K : ℝ) + 1) * δ))
            ≤ renewalMeasure μ (Set.Icc y (y + 2 * (K : ℝ) * δ))
              + renewalMeasure μ (Set.Icc (y + 2 * (K : ℝ) * δ)
                  (y + 2 * ((K : ℝ) + 1) * δ)) := measure_union_le _ _
          _ ≤ ENNReal.ofReal (((K : ℝ) + 1) * D) + ENNReal.ofReal D := add_le_add h1 h2
          _ = ENNReal.ofReal (((K : ℝ) + 1) * D + D) :=
              (ENNReal.ofReal_add (by positivity) hD0).symm
          _ = ENNReal.ofReal ((((K : ℝ) + 1) + 1) * D) := by ring_nf
  -- choose enough cells to cover an interval of length `ℓ`
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ℓ ≤ 2 * (K : ℝ) * δ := by
    refine ⟨⌈ℓ / (2 * δ)⌉₊, ?_⟩
    have h1 : ℓ / (2 * δ) ≤ (⌈ℓ / (2 * δ)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (0 : ℝ) < 2 * δ := by linarith
    rw [div_le_iff₀ h2] at h1
    linarith
  refine ⟨((K : ℝ) + 1) * D, ?_⟩
  filter_upwards [key K] with y hy
  refine le_trans (measure_mono ?_) hy
  exact Set.Icc_subset_Icc le_rfl (by linarith)

/-- **The two-sided uniform cell bound** (A-4e′): under a finite exponential
moment, `U([y, y+ℓ]) ≤ C` for **every** `y ∈ ℝ`, not just for large `y`.

The two tails are bounded by completely different arguments, and this is the point
of the statement: on the right, `exists_bound_renewalMeasure_Icc_atTop_of_length`
— an Abel/Fourier renewal estimate, which needs `μ` nonlattice with a second
moment and positive drift; on the left, the Chernoff bound
`renewalMeasure_le_of_expTransform`, which needs `∫e^{-θz}dμ < 1` at some `θ > 0`
and gives the *monotone* bound `e^{θb}(1-λ)⁻¹` on all of `(-∞, b]` at once. Since
the eventual bound holds past some `y₀`, the whole left part `y ≤ y₀` is a single
half-line and one Chernoff constant covers it.

The exponential-moment hypothesis is essential and cannot be dropped: with only
nonlattice + `MemLp id 2 μ` there is nothing to bound `U` near `−∞`. The chapter
supplies it, since the increment law is the Cramér tilt. -/
theorem exists_bound_renewalMeasure_Icc_of_expTransform {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {θ : ℝ} (hθ : 0 < θ) (hlt : expTransform θ μ < 1) (ℓ : ℝ) :
    ∃ C : ℝ, ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + ℓ)) ≤ ENNReal.ofReal C := by
  obtain ⟨C₁, hC₁⟩ := exists_bound_renewalMeasure_Icc_atTop_of_length hμ hint hm ℓ
  obtain ⟨y₀, hy₀⟩ := Filter.eventually_atTop.1 hC₁
  -- the left half-line `(-∞, b]`, covered in one shot by the Chernoff bound
  set b : ℝ := y₀ + max ℓ 0 with hbdef
  set E : ℝ≥0∞ := ENNReal.ofReal (Real.exp (θ * b)) * (1 - expTransform θ μ)⁻¹ with hEdef
  have hEfin : E ≠ ∞ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hlt))).ne
  refine ⟨max C₁ E.toReal, fun y => ?_⟩
  rcases le_or_gt y₀ y with hy | hy
  · exact (hy₀ y hy).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · have hsub : Set.Icc y (y + ℓ) ⊆ Set.Iic b := by
      intro x hx
      have := hx.2
      simp only [Set.mem_Iic, hbdef]
      have hℓ : ℓ ≤ max ℓ 0 := le_max_left _ _
      linarith [hy.le]
    calc renewalMeasure μ (Set.Icc y (y + ℓ)) ≤ E :=
          renewalMeasure_le_of_expTransform hθ measurableSet_Icc hsub
      _ = ENNReal.ofReal E.toReal := (ENNReal.ofReal_toReal hEfin).symm
      _ ≤ ENNReal.ofReal (max C₁ E.toReal) := ENNReal.ofReal_le_ofReal (le_max_right _ _)

/-- **The renewal limit for a general bandlimited kernel**, with `sincSq` as the
reference kernel: if the smoothed renewal series of `w` converges pointwise to `S`,
then `S y ⟶ (∫w)/m̂`.

Every abstract reference-kernel hypothesis of
`tendsto_of_tendsto_sum_integral_comp_sub_bandlimited` is discharged here, so the
only remaining hypotheses are on `w` itself: continuity, `w, 𝓕w ∈ L¹`,
bandlimitedness, and the Lipschitz bound `‖𝓕w(t) − 𝓕w(0)‖ ≤ L|t|`. -/
theorem tendsto_of_tendsto_sum_integral_comp_sub_sincSq {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {w : ℝ → ℂ} {Tw Lw : ℝ} (hwc : Continuous w) (hwi : Integrable w)
    (hFw : Integrable (𝓕 w)) (hwT : ∀ t : ℝ, Tw < |t| → 𝓕 w t = 0)
    (hwL : ∀ t : ℝ, ‖𝓕 w t - 𝓕 w 0‖ ≤ Lw * |t|) (hLw0 : 0 ≤ Lw)
    {S : ℝ → ℂ}
    (hS : ∀ y : ℝ, Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, ∫ z, w (y - z) ∂(convPow μ n))
      Filter.atTop (nhds (S y))) :
    Filter.Tendsto S Filter.atTop (nhds ((∫ x, w x) / ((∫ x, x ∂μ : ℝ) : ℂ))) :=
  tendsto_of_tendsto_sum_integral_comp_sub_bandlimited (Bκ := 8) (Tκ := 2) (Lκ := 1)
    hμ hint hm sincSq_nonneg sincSq_le_eight continuous_sincSq integrable_sincSq
    integrable_fourier_ofReal_sincSq (fun _ ht => fourier_ofReal_sincSq_eq_zero ht)
    norm_fourier_ofReal_sincSq_sub_le zero_le_one integral_sincSq_pos
    hwc hwi hFw hwT hwL hLw0 hS

end Renewal

end AbsorptionCutoff
end

section
-- module Solutions.OAIQ247_JB.Supercritical_RenewalApprox
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Bandlimited approximation in the directly-Riemann-integrable norm

Split out of `AbsorptionCutoff.Supercritical.RenewalSinc` purely for build time, at the
point where that module reached 613 lines and 80 s: the material below is the
*growing* end of the argument, while its base — the concrete renewal limits at
`sincSq` and the uniform cell bound — is finished and only consumed here.

The key renewal theorem is reached by approximating a directly Riemann integrable
kernel by *bandlimited* ones in `Renewal.driNorm`, for which
`AbsorptionCutoff.Supercritical.Renewal` already supplies the error estimate. This module
builds the approximants: the rescaled approximate identity `K_a` and the smoothing
`w ⋆ K_a`, which is bandlimited at `2a` for every integrable `w` and converges to
`w` uniformly, with a far field that decays fast enough to be summable over the
unit cells.

## Main results

* `Renewal.smoothKernel`: the rescaled approximate identity `(a/2)·sincSq(a·)`,
  with unit mass, `4a/(1+a²t²)` decay and band `[-2a, 2a]`.
* `Renewal.smoothed`: the smoothing `w ⋆ K_a`, bandlimited at `2a`
  (`Renewal.fourier_smoothed_eq_zero`).
* `Renewal.exists_forall_norm_smoothed_sub_le`: `‖w ⋆ K_a − w‖_∞ → 0` for
  continuous compactly supported `w`.
* `Renewal.norm_smoothed_le_of_support`: the far field of `w ⋆ K_a` decays like
  `(a·dist²)⁻¹`, which is what makes the far cells summable.
* `Renewal.exists_driNorm_smoothed_sub_lt`: the two regimes combined —
  `‖w − w ⋆ K_a‖_DRI` is arbitrarily small for large `a`.
* `Renewal.fourier_ofReal_smoothKernel`: `𝓕K_a(ξ) = ½·𝓕(sincSq)(ξ/a)`, whence
  `𝓕K_a(0) = 1` and the Lipschitz-at-`0` bound with constant `1/(2a)`.
* `Renewal.tendsto_tsum_integral_comp_sub_of_driNorm`: **the key renewal theorem**
  for continuous directly Riemann integrable kernels,
  `∑ₙ ∫ z(y−s) μ^{*n}(ds) ⟶ (∫z)/m̂`.
-/

open MeasureTheory
open scoped Convolution ENNReal NNReal FourierTransform

namespace AbsorptionCutoff

namespace Renewal

/-! ### The rescaled approximate identity

The d.R.i. approximation argument convolves with a *concentrating* kernel that is
still bandlimited. Both halves come from `sincSq` by dilation: compressing by `a`
concentrates the mass at the origin while stretching the band from `[-2,2]` to
`[-2a, 2a]`, which is harmless — the renewal limit holds for *every* band. -/

lemma smoothKernel_nonneg {a : ℝ} (ha : 0 ≤ a) (t : ℝ) : 0 ≤ smoothKernel a t :=
  mul_nonneg (by linarith) (sincSq_nonneg _)

lemma continuous_smoothKernel (a : ℝ) : Continuous (smoothKernel a) :=
  continuous_const.mul (continuous_sincSq.comp (continuous_const.mul continuous_id))

lemma integrable_smoothKernel {a : ℝ} (ha : 0 < a) : Integrable (smoothKernel a) :=
  (integrable_sincSq.comp_mul_left' (ne_of_gt ha)).const_mul (a / 2)

/-- **Unit mass**: `∫ K_a = (a/2)·a⁻¹·∫sincSq = (a/2)·a⁻¹·2 = 1`. -/
theorem integral_smoothKernel {a : ℝ} (ha : 0 < a) : ∫ t : ℝ, smoothKernel a t = 1 := by
  have hdil : (∫ t : ℝ, sincSq (a * t)) = |a⁻¹| • ∫ x : ℝ, sincSq x :=
    Measure.integral_comp_mul_left sincSq a
  simp only [smoothKernel]
  rw [integral_const_mul, hdil, integral_sincSq, abs_of_pos (inv_pos.2 ha), smul_eq_mul]
  field_simp

/-- **Decay**: `K_a(t) ≤ 4a/(1 + a²t²)`, hence `≤ 4/(a t²)` away from the origin.
The `t^{-2}` tail is what makes the far cells summable in the d.R.i. norm, with a
total of size `O(1/(aM))` beyond `|t| ≥ M`. -/
lemma smoothKernel_le {a : ℝ} (ha : 0 < a) (t : ℝ) :
    smoothKernel a t ≤ 4 * a * (1 + (a * t) ^ 2)⁻¹ := by
  have h := sincSq_le (a * t)
  have ha2 : 0 < a / 2 := by linarith
  calc smoothKernel a t = (a / 2) * sincSq (a * t) := rfl
    _ ≤ (a / 2) * (8 * (1 + (a * t) ^ 2)⁻¹) := by
        exact mul_le_mul_of_nonneg_left h (le_of_lt ha2)
    _ = 4 * a * (1 + (a * t) ^ 2)⁻¹ := by ring

/-- `K_a` as a rescaled copy of `sincSq`, in the form the transform rules want. -/
lemma ofReal_smoothKernel_eq (a : ℝ) :
    (fun t : ℝ => ((smoothKernel a t : ℝ) : ℂ))
      = fun t : ℝ => ((a / 2 : ℝ) : ℂ) * (fun u : ℝ => ((sincSq u : ℝ) : ℂ)) (a * t) := by
  funext t
  simp only [smoothKernel]
  push_cast
  ring

/-- **The transform of `K_a` in closed form**: `𝓕K_a(ξ) = ½·𝓕(sincSq)(ξ/a)`.

The two `a`'s cancel — the `a/2` normalization against the `a⁻¹` of the dilation
rule — which is exactly why `K_a` has unit mass for every `a` while its band
stretches. Both the value at the origin and the Lipschitz bound below are read off
this. -/
theorem fourier_ofReal_smoothKernel {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    𝓕 (fun t : ℝ => ((smoothKernel a t : ℝ) : ℂ)) ξ
      = (1 / 2 : ℂ) * 𝓕 (fun x : ℝ => ((sincSq x : ℝ) : ℂ)) (ξ / a) := by
  have hdil := fourier_comp_mul_left (fun u : ℝ => ((sincSq u : ℝ) : ℂ)) ha ξ
  rw [ofReal_smoothKernel_eq a, fourier_const_mul, hdil, Complex.real_smul, ← mul_assoc]
  congr 1
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  push_cast
  field_simp

/-- **The band**: `𝓕K_a` vanishes outside `[-2a, 2a]`, by
`fourier_comp_mul_left_eq_zero` applied to the `[-2,2]` band of `𝓕(sincSq)`. -/
theorem fourier_ofReal_smoothKernel_eq_zero {a : ℝ} (ha : 0 < a) {ξ : ℝ} (hξ : 2 * a < |ξ|) :
    𝓕 (fun t : ℝ => ((smoothKernel a t : ℝ) : ℂ)) ξ = 0 := by
  rw [ofReal_smoothKernel_eq a, fourier_const_mul,
    fourier_comp_mul_left_eq_zero ha (fun _ ht => fourier_ofReal_sincSq_eq_zero ht)
      (by rwa [mul_comm a 2]), mul_zero]

/-- `𝓕K_a(0) = ∫K_a = 1`, for every `a > 0`. -/
theorem fourier_ofReal_smoothKernel_zero {a : ℝ} (ha : 0 < a) :
    𝓕 (fun t : ℝ => ((smoothKernel a t : ℝ) : ℂ)) 0 = 1 := by
  have hofReal : (∫ x : ℝ, ((smoothKernel a x : ℝ) : ℂ))
      = ((∫ x : ℝ, smoothKernel a x : ℝ) : ℂ) := integral_ofReal
  rw [fourier_zero_eq_integral, hofReal, integral_smoothKernel ha]
  norm_num

/-- **`𝓕K_a` is Lipschitz at the origin with constant `1/(2a)`.**

This is the hypothesis that `tendsto_of_tendsto_sum_integral_comp_sub_sincSq`
needs and that the smoothing inherits; the constant *improves* as the kernel
concentrates. -/
theorem norm_fourier_ofReal_smoothKernel_sub_le {a : ℝ} (ha : 0 < a) (t : ℝ) :
    ‖𝓕 (fun x : ℝ => ((smoothKernel a x : ℝ) : ℂ)) t
      - 𝓕 (fun x : ℝ => ((smoothKernel a x : ℝ) : ℂ)) 0‖ ≤ 1 / (2 * a) * |t| := by
  rw [fourier_ofReal_smoothKernel ha, fourier_ofReal_smoothKernel ha, zero_div, ← mul_sub,
    norm_mul]
  have h := norm_fourier_ofReal_sincSq_sub_le (t / a)
  rw [one_mul, abs_div, abs_of_pos ha] at h
  have hnorm : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hnorm]
  calc 1 / 2 * ‖𝓕 (fun x : ℝ => ((sincSq x : ℝ) : ℂ)) (t / a)
        - 𝓕 (fun x : ℝ => ((sincSq x : ℝ) : ℂ)) 0‖
      ≤ 1 / 2 * (|t| / a) := by linarith
    _ = 1 / (2 * a) * |t| := by field_simp

lemma integrable_ofReal_smoothKernel {a : ℝ} (ha : 0 < a) :
    Integrable (fun t : ℝ => ((smoothKernel a t : ℝ) : ℂ)) :=
  (integrable_smoothKernel ha).ofReal

/-- **The smoothing is bandlimited, at band `2a`** (A-5b-3, part 1).

This is the only place the convolution is really needed: `𝓕(w ⋆ K_a) = 𝓕w · 𝓕K_a`
kills everything outside `K_a`'s band regardless of how rough `w` is. Crucially
`Real.fourier_mul_convolution_eq` asks only for **integrability** of the two
factors — no Schwartz class, no smoothness — so this applies to a merely
continuous, compactly supported `w`. -/
theorem fourier_smoothed_eq_zero {w : ℝ → ℂ} (hw : Integrable w) {a : ℝ} (ha : 0 < a)
    {ξ : ℝ} (hξ : 2 * a < |ξ|) : 𝓕 (smoothed w a) ξ = 0 := by
  rw [smoothed, Real.fourier_mul_convolution_eq hw (integrable_ofReal_smoothKernel ha) ξ,
    fourier_ofReal_smoothKernel_eq_zero ha hξ, mul_zero]

/-- **The mass `K_a` leaves outside a fixed window is `O(1/a)`** (A-5b-3b, step 1).

Off `[-δ, δ]` the kernel is dominated by a *fixed* integrable profile times `1/a`:

  `K_a(u) ≤ (4(1+δ²)/(aδ²)) · (1+u²)⁻¹`   for `δ < |u|`,

because `a²δ²(1+u²) ≤ (1+δ²)(1+a²u²)` once `δ² < u²`. Comparing to
`(1+u²)⁻¹`, whose integral over all of `ℝ` is `π`, keeps the whole estimate inside
`Mathlib`'s elementary integral API — no improper integral of `u^{-2}` and no
reflection of a half-line is needed.

Note this is where the *tail mass* is the right tool, unlike the far-field
estimate `norm_smoothed_le_of_support`, which must use `K_a`'s pointwise decay. -/
theorem setIntegral_smoothKernel_compl_le {δ : ℝ} (hδ : 0 < δ) {a : ℝ} (ha : 0 < a) :
    ∫ u in {u : ℝ | δ < |u|}, smoothKernel a u ≤ 4 * (1 + δ ^ 2) * Real.pi / (a * δ ^ 2) := by
  set C : ℝ := 4 * (1 + δ ^ 2) / (a * δ ^ 2) with hC
  have hCpos : 0 < C := by positivity
  have hpt : ∀ u ∈ {u : ℝ | δ < |u|}, smoothKernel a u ≤ C * (1 + u ^ 2)⁻¹ := by
    intro u hu
    replace hu : δ < |u| := hu
    refine (smoothKernel_le ha u).trans ?_
    have hu2 : δ ^ 2 < u ^ 2 := by
      rw [← sq_abs u]; exact pow_lt_pow_left₀ hu hδ.le two_ne_zero
    have h1 : (0 : ℝ) < 1 + (a * u) ^ 2 := by positivity
    have h2 : (0 : ℝ) < 1 + u ^ 2 := by positivity
    have h3 : (0 : ℝ) < a * δ ^ 2 := by positivity
    rw [hC, div_mul_eq_mul_div, ← sub_nonneg]
    have expand : 4 * (1 + δ ^ 2) * (1 + u ^ 2)⁻¹ / (a * δ ^ 2) - 4 * a * (1 + (a * u) ^ 2)⁻¹
        = 4 * ((1 + δ ^ 2) * (1 + (a * u) ^ 2) - a ^ 2 * δ ^ 2 * (1 + u ^ 2))
            / (a * δ ^ 2 * (1 + u ^ 2) * (1 + (a * u) ^ 2)) := by
      field_simp
    rw [expand]
    have key : a ^ 2 * δ ^ 2 * (1 + u ^ 2) ≤ (1 + δ ^ 2) * (1 + (a * u) ^ 2) := by nlinarith
    exact div_nonneg (by linarith) (by positivity)
  have hmeas : MeasurableSet {u : ℝ | δ < |u|} :=
    measurableSet_lt measurable_const measurable_norm
  calc ∫ u in {u : ℝ | δ < |u|}, smoothKernel a u
      ≤ ∫ u in {u : ℝ | δ < |u|}, C * (1 + u ^ 2)⁻¹ :=
        setIntegral_mono_on (integrable_smoothKernel ha).integrableOn
          (integrable_inv_one_add_sq.const_mul C).integrableOn hmeas hpt
    _ ≤ ∫ u : ℝ, C * (1 + u ^ 2)⁻¹ :=
        setIntegral_le_integral (integrable_inv_one_add_sq.const_mul C)
          (Filter.Eventually.of_forall fun u => by positivity)
    _ = 4 * (1 + δ ^ 2) * Real.pi / (a * δ ^ 2) := by
        rw [integral_const_mul, integral_univ_inv_one_add_sq, hC]
        ring

lemma smoothed_apply (w : ℝ → ℂ) (a x : ℝ) :
    smoothed w a x = ∫ u : ℝ, w u * ((smoothKernel a (x - u) : ℝ) : ℂ) := by
  rw [smoothed, convolution_def]
  rfl

/-- The symmetric form of the smoothing, `∫ w(x−u)K_a(u)du`, obtained from
`convolution_mul_swap` — which avoids reflecting the measure, so no
`volume.IsNegInvariant` instance is needed. -/
lemma smoothed_apply' (w : ℝ → ℂ) (a x : ℝ) :
    smoothed w a x = ∫ u : ℝ, w (x - u) * ((smoothKernel a u : ℝ) : ℂ) :=
  convolution_mul_swap

/-- **The smoothing converges uniformly** (A-5b-3b): for continuous compactly
supported `w`, `‖w ⋆ K_a − w‖_∞ ≤ ε` once `a` is large.

Since `∫K_a = 1`, the difference is the single integral
`∫ (w(x−u) − w(x))K_a(u)du`, and the integrand is bounded by

  `(ε/2)·K_a(u) + 2‖w‖_∞·1_{|u| > δ}·K_a(u)`,

with `δ` from uniform continuity of `w` (`HasCompactSupport.uniformContinuous_of_continuous`)
and the second term controlled by `setIntegral_smoothKernel_compl_le`. The bound
is uniform in `x` because both `δ` and `‖w‖_∞` are. -/
theorem exists_forall_norm_smoothed_sub_le {w : ℝ → ℂ} (hwc : Continuous w)
    (hws : HasCompactSupport w) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ a, A ≤ a → ∀ x : ℝ, ‖smoothed w a x - w x‖ ≤ ε := by
  obtain ⟨M, hM⟩ := hws.exists_bound_of_continuous hwc
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  obtain ⟨δ₀, hδ₀, hδw⟩ := Metric.uniformContinuous_iff.1
    (hws.uniformContinuous_of_continuous hwc) (ε / 2) (by linarith)
  -- split at `δ₀/2`, so that `|u| ≤ δ` gives the *strict* inequality uniform continuity wants
  set δ : ℝ := δ₀ / 2 with hδdef
  have hδ : 0 < δ := by positivity
  refine ⟨max 1 (16 * M * (1 + δ ^ 2) * Real.pi / (ε * δ ^ 2)), lt_of_lt_of_le one_pos
    (le_max_left _ _), fun a hA x => ?_⟩
  have ha : 0 < a := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hA)
  have hmeas : MeasurableSet {u : ℝ | δ < |u|} :=
    measurableSet_lt measurable_const measurable_norm
  -- the difference is a single integral against `K_a`, since `∫K_a = 1`
  have hKint := integrable_smoothKernel ha
  have hbdd : ∀ u : ℝ, ‖w (x - u) * ((smoothKernel a u : ℝ) : ℂ)‖ ≤ M * smoothKernel a u := by
    intro u
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (smoothKernel_nonneg ha.le _)]
    exact mul_le_mul_of_nonneg_right (hM _) (smoothKernel_nonneg ha.le _)
  have hint1 : Integrable fun u : ℝ => w (x - u) * ((smoothKernel a u : ℝ) : ℂ) := by
    refine Integrable.mono' (hKint.const_mul M)
      (((hwc.comp (continuous_const.sub continuous_id)).mul
        (Complex.continuous_ofReal.comp (continuous_smoothKernel a))).aestronglyMeasurable)
      (Filter.Eventually.of_forall hbdd)
  have hofReal : (∫ u : ℝ, ((smoothKernel a u : ℝ) : ℂ))
      = ((∫ u : ℝ, smoothKernel a u : ℝ) : ℂ) := integral_ofReal
  have hconst : (∫ u : ℝ, w x * ((smoothKernel a u : ℝ) : ℂ)) = w x := by
    rw [integral_const_mul, hofReal, integral_smoothKernel ha]
    simp
  have hsplit : (∫ u : ℝ, (w (x - u) - w x) * ((smoothKernel a u : ℝ) : ℂ))
      = smoothed w a x - w x := by
    have hlin : (∫ u : ℝ, (w (x - u) - w x) * ((smoothKernel a u : ℝ) : ℂ))
        = (∫ u : ℝ, w (x - u) * ((smoothKernel a u : ℝ) : ℂ))
          - ∫ u : ℝ, w x * ((smoothKernel a u : ℝ) : ℂ) := by
      refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => ?_))
        (integral_sub hint1 ((hKint.ofReal).const_mul (w x)))
      dsimp only
      ring
    rw [hlin, hconst, smoothed_apply']
  -- the dominating function
  set g : ℝ → ℝ := fun u => ε / 2 * smoothKernel a u
    + 2 * M * Set.indicator {u : ℝ | δ < |u|} (smoothKernel a) u with hg
  have hgint : Integrable g :=
    (hKint.const_mul _).add ((hKint.indicator hmeas).const_mul _)
  have hdom : ∀ u : ℝ, ‖(w (x - u) - w x) * ((smoothKernel a u : ℝ) : ℂ)‖ ≤ g u := by
    intro u
    have hK0 : 0 ≤ smoothKernel a u := smoothKernel_nonneg ha.le _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK0]
    by_cases hu : δ < |u|
    · have h2M : ‖w (x - u) - w x‖ ≤ 2 * M :=
        le_trans (norm_sub_le _ _) (by linarith [hM (x - u), hM x])
      have : Set.indicator {u : ℝ | δ < |u|} (smoothKernel a) u = smoothKernel a u := by
        rw [Set.indicator_apply, if_pos (show u ∈ {u : ℝ | δ < |u|} from hu)]
      rw [hg]
      simp only [this]
      nlinarith [mul_nonneg hε.le hK0]
    · have hdist : dist (x - u) x < δ₀ := by
        rw [Real.dist_eq, sub_sub_cancel_left, abs_neg]
        have := not_lt.1 hu
        rw [hδdef] at this
        linarith
      have hsmall : ‖w (x - u) - w x‖ ≤ ε / 2 := by
        have := hδw hdist
        rw [dist_eq_norm] at this
        linarith
      have : Set.indicator {u : ℝ | δ < |u|} (smoothKernel a) u = 0 := by
        rw [Set.indicator_apply, if_neg (show u ∉ {u : ℝ | δ < |u|} from hu)]
      rw [hg]
      simp only [this]
      nlinarith
  rw [← hsplit]
  refine le_trans (norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall hdom)) ?_
  -- evaluate the dominating integral
  rw [hg, integral_add ((hKint.const_mul _)) ((hKint.indicator hmeas).const_mul _),
    integral_const_mul, integral_const_mul, integral_indicator hmeas, integral_smoothKernel ha,
    mul_one]
  have htail : ∫ u in {u : ℝ | δ < |u|}, smoothKernel a u
      ≤ 4 * (1 + δ ^ 2) * Real.pi / (a * δ ^ 2) := setIntegral_smoothKernel_compl_le hδ ha
  have hnum : 16 * M * (1 + δ ^ 2) * Real.pi / (ε * δ ^ 2) ≤ a := (le_max_right _ _).trans hA
  have hpos : (0 : ℝ) < ε * δ ^ 2 := by positivity
  rw [div_le_iff₀ hpos] at hnum
  have hfin : 2 * M * (4 * (1 + δ ^ 2) * Real.pi / (a * δ ^ 2)) ≤ ε / 2 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity : (0 : ℝ) < a * δ ^ 2)]
    nlinarith [Real.pi_pos]
  have hmono : 2 * M * (∫ u in {u : ℝ | δ < |u|}, smoothKernel a u)
      ≤ 2 * M * (4 * (1 + δ ^ 2) * Real.pi / (a * δ ^ 2)) :=
    mul_le_mul_of_nonneg_left htail (by linarith)
  linarith

/-- **The far field of a smoothing decays like `(a·dist²)⁻¹`** (A-5b-3, part 3a).

If `w` is supported in `[-R, R]` then, beyond that interval,

  `‖(w ⋆ K_a)(x)‖ ≤ 4‖w‖_{L¹} / (a(|x| − R)²)`.

**The exponent `2` matters and the naive estimate does not suffice.** Bounding the
far field by the *tail mass* `∫_{|u| ≥ s} K_a = O(1/(as))` gives only a `1/|x|`
decay, whose cell sums over `ℤ` diverge — the far cells would contribute a
harmonic series. Using instead the *pointwise* decay of `K_a` against the total
mass of `w` gives `1/|x|²`, whose cell sums converge to a constant **independent
of `R`**; the whole far field is then `O(‖w‖_{L¹}/a)` and vanishes as `a → ∞`,
with `R` fixed first. -/
theorem norm_smoothed_le_of_support {w : ℝ → ℂ} (hw : Integrable w) {R : ℝ}
    (hsupp : ∀ u : ℝ, R < |u| → w u = 0) {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : R < |x|) :
    ‖smoothed w a x‖ ≤ (∫ u : ℝ, ‖w u‖) * (4 / (a * (|x| - R) ^ 2)) := by
  have hd : 0 < |x| - R := by linarith
  have hbound : ∀ u : ℝ, ‖w u * ((smoothKernel a (x - u) : ℝ) : ℂ)‖
      ≤ ‖w u‖ * (4 / (a * (|x| - R) ^ 2)) := by
    intro u
    by_cases hu : R < |u|
    · simp [hsupp u hu]
    · replace hu : |u| ≤ R := not_lt.1 hu
      have hxu : |x| - R ≤ |x - u| := by
        have := abs_sub_abs_le_abs_sub x u
        linarith
      have hxu0 : 0 < |x - u| := lt_of_lt_of_le hd hxu
      have hsq : a ^ 2 * (|x| - R) ^ 2 ≤ 1 + (a * (x - u)) ^ 2 := by
        have h1 : (|x| - R) ^ 2 ≤ (x - u) ^ 2 := by
          rw [← sq_abs (x - u)]
          exact pow_le_pow_left₀ hd.le hxu 2
        nlinarith [sq_nonneg a]
      have hker : smoothKernel a (x - u) ≤ 4 / (a * (|x| - R) ^ 2) := by
        refine (smoothKernel_le ha (x - u)).trans ?_
        have hpos : (0 : ℝ) < a ^ 2 * (|x| - R) ^ 2 := by positivity
        have hinv : (1 + (a * (x - u)) ^ 2)⁻¹ ≤ (a ^ 2 * (|x| - R) ^ 2)⁻¹ := inv_anti₀ hpos hsq
        calc 4 * a * (1 + (a * (x - u)) ^ 2)⁻¹ ≤ 4 * a * (a ^ 2 * (|x| - R) ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_left hinv (by positivity)
          _ = 4 / (a * (|x| - R) ^ 2) := by field_simp
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (smoothKernel_nonneg ha.le _)]
      exact mul_le_mul_of_nonneg_left hker (norm_nonneg _)
  rw [smoothed_apply]
  refine le_trans (norm_integral_le_of_norm_le (hw.norm.mul_const _)
    (Filter.Eventually.of_forall hbound)) ?_
  rw [integral_mul_const]

/-! ### The d.R.i. error of the smoothing

The two regimes of the previous two estimates are now summed over the unit cells.
On the finitely many cells meeting the support, the *uniform* bound of
`exists_forall_norm_smoothed_sub_le` applies; on the rest `w` vanishes and the far
field of `norm_smoothed_le_of_support` is dominated by a constant multiple of the
reference profile `(1+x²)⁻¹`, whose d.R.i. norm is finite. -/

/-- A compactly supported kernel vanishes outside some `[-R, R]` with `R ≥ 0`. -/
lemma exists_radius_of_hasCompactSupport {w : ℝ → ℂ} (hws : HasCompactSupport w) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : ℝ, R < |x| → w x = 0 := by
  obtain ⟨r, hr⟩ := hws.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨max r 0, le_max_right _ _, fun x hx => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have h := hr hmem
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
  have hx' : max r 0 < |x| := hx
  linarith [le_max_left r (0 : ℝ)]

/-- **The smoothing converges in the d.R.i. norm** (A-5b-3c): a continuous
compactly supported kernel is approximated by its own smoothings, to any accuracy
in `‖·‖_DRI`.

Combined with the cutoff step this is the whole approximation half of the minimal
route: `smoothed w a` is bandlimited (`fourier_smoothed_eq_zero`), so a d.R.i.
kernel is `‖·‖_DRI`-approximable by bandlimited ones, which is what transports the
renewal limit.

The far cells are where the argument could fail and does not: `w` vanishes there,
so the error is the far field `4‖w‖_{L¹}/(a(|x|−R)²)`, and the exponent `2` — not
the `1` a tail-mass estimate would give — makes it dominated by `(C/a)(1+x²)⁻¹`
with `C` independent of `a`. Summing over cells then costs only the *finite*
`driNorm ((1+x²)⁻¹)`. -/
theorem exists_driNorm_smoothed_sub_lt {w : ℝ → ℂ} (hwc : Continuous w)
    (hws : HasCompactSupport w) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ driNorm (fun x => ‖w x - smoothed w a x‖ₑ) < ENNReal.ofReal ε := by
  obtain ⟨R, hR0, hR⟩ := exists_radius_of_hasCompactSupport hws
  have hwi : Integrable w := hwc.integrable_of_hasCompactSupport hws
  set L : ℝ := ∫ u : ℝ, ‖w u‖ with hLdef
  have hL0 : 0 ≤ L := integral_nonneg fun _ => norm_nonneg _
  set C : ℝ := 4 * L * (1 + (1 + R) ^ 2) with hCdef
  have hC0 : 0 ≤ C := by positivity
  -- the reference profile, of finite d.R.i. norm
  set p : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (1 + x ^ 2)⁻¹ with hpdef
  set D : ℝ := (driNorm p).toReal with hDdef
  have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
  have hDeq : driNorm p = ENNReal.ofReal D :=
    (ENNReal.ofReal_toReal driNorm_ofReal_inv_one_add_sq_ne_top).symm
  -- the finitely many cells that can meet the support
  set S : Finset ℤ := Finset.Icc (-((⌈R⌉₊ + 2 : ℕ) : ℤ)) ((⌈R⌉₊ + 2 : ℕ) : ℤ) with hSdef
  set M : ℕ := S.card with hMdef
  set ε₁ : ℝ := ε / (3 * (M + 1)) with hε₁def
  have hMcast : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hden : (0 : ℝ) < 3 * ((M : ℝ) + 1) := by linarith
  have hε₁0 : 0 < ε₁ := by rw [hε₁def]; exact div_pos hε hden
  obtain ⟨A, hA0, hA⟩ := exists_forall_norm_smoothed_sub_le hwc hws hε₁0
  set a : ℝ := max A (max 1 (3 * C * D / ε)) with hadef
  have ha : 0 < a := lt_of_lt_of_le one_pos ((le_max_left _ _).trans (le_max_right A _))
  have haA : A ≤ a := le_max_left _ _
  have haC : 3 * C * D / ε ≤ a := (le_max_right _ _).trans (le_max_right A _)
  refine ⟨a, ha, ?_⟩
  -- the cellwise bound, split into the two regimes
  have hcell : ∀ k : ℤ, cellSup (fun x => ‖w x - smoothed w a x‖ₑ) k
      ≤ Set.indicator (↑S : Set ℤ) (fun _ => ENNReal.ofReal ε₁) k
        + Set.indicator ((↑S : Set ℤ)ᶜ)
            (fun k => ENNReal.ofReal (C / a) * cellSup p k) k := by
    intro k
    by_cases hk : k ∈ S
    · rw [Set.indicator_of_mem (Finset.mem_coe.2 hk),
        Set.indicator_of_notMem
          (fun hc => (Set.mem_compl_iff _ _).1 hc (Finset.mem_coe.2 hk)), add_zero]
      refine iSup₂_le fun x _ => ?_
      change ‖w x - smoothed w a x‖ₑ ≤ ENNReal.ofReal ε₁
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (by rw [norm_sub_rev]; exact hA a haA x)
    · rw [Set.indicator_of_notMem (fun h => hk (Finset.mem_coe.1 h)),
        Set.indicator_of_mem (Set.mem_compl fun h => hk (Finset.mem_coe.1 h)), zero_add]
      refine iSup₂_le fun x hx => ?_
      -- on this cell `w` vanishes and only the far field survives
      rw [Set.mem_Icc] at hx
      have hkint : ((⌈R⌉₊ + 2 : ℕ) : ℤ) + 1 ≤ |k| := by
        rw [hSdef, Finset.mem_Icc] at hk
        rcases le_or_gt 0 k with hk0 | hk0
        · rw [abs_of_nonneg hk0]; omega
        · rw [abs_of_neg hk0]; omega
      have hkR : (⌈R⌉₊ : ℝ) + 3 ≤ |(k : ℝ)| := by
        have hcast : ((((⌈R⌉₊ + 2 : ℕ) : ℤ) + 1 : ℤ) : ℝ) ≤ ((|k| : ℤ) : ℝ) := by
          exact_mod_cast hkint
        rw [Int.cast_abs] at hcast
        push_cast at hcast
        linarith
      have hRle : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
      have hxabs : R + 1 ≤ |x| := by
        rcases le_or_gt 0 ((k : ℝ)) with hk0 | hk0
        · rw [abs_of_nonneg hk0] at hkR
          rw [abs_of_nonneg (by linarith [hx.1])]
          linarith [hx.1]
        · rw [abs_of_neg hk0] at hkR
          rw [abs_of_nonpos (by linarith [hx.2])]
          linarith [hx.2]
      have hxR : R < |x| := by linarith
      have hw0 : w x = 0 := hR x hxR
      have hfar := norm_smoothed_le_of_support hwi hR ha hxR
      -- dominate the far field by the reference profile
      have ht1 : (1 : ℝ) ≤ |x| - R := by linarith
      have ht2 : (1 : ℝ) ≤ (|x| - R) ^ 2 := by nlinarith [ht1]
      have ht3 : |x| - R ≤ (|x| - R) ^ 2 := by nlinarith [ht1]
      have hkey : 1 + x ^ 2 ≤ (1 + (1 + R) ^ 2) * (|x| - R) ^ 2 := by
        rw [← sq_abs x]
        nlinarith [mul_le_mul_of_nonneg_left ht3 (by linarith : (0 : ℝ) ≤ 2 * R),
          mul_le_mul_of_nonneg_left ht2 (sq_nonneg R), ht2]
      have hdom : L * (4 / (a * (|x| - R) ^ 2)) ≤ C / a * (1 + x ^ 2)⁻¹ := by
        have hp1 : (0 : ℝ) < a * (|x| - R) ^ 2 := by positivity
        have hp2 : (0 : ℝ) < a * (1 + x ^ 2) := by positivity
        rw [show L * (4 / (a * (|x| - R) ^ 2)) = (4 * L) / (a * (|x| - R) ^ 2) by ring,
          show C / a * (1 + x ^ 2)⁻¹ = C / (a * (1 + x ^ 2)) by field_simp,
          div_le_div_iff₀ hp1 hp2, hCdef]
        nlinarith [mul_le_mul_of_nonneg_left hkey (by positivity : (0 : ℝ) ≤ 4 * L * a)]
      calc ‖w x - smoothed w a x‖ₑ = ENNReal.ofReal ‖smoothed w a x‖ := by
            rw [hw0, zero_sub, enorm_neg, ofReal_norm]
        _ ≤ ENNReal.ofReal (C / a * (1 + x ^ 2)⁻¹) :=
            ENNReal.ofReal_le_ofReal (le_trans hfar hdom)
        _ = ENNReal.ofReal (C / a) * p x := by
            rw [hpdef, ← ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal (C / a) * cellSup p k := by
            gcongr
            exact le_cellSup ⟨hx.1, hx.2⟩
  -- sum the two regimes
  have hnear : (∑' k : ℤ, Set.indicator (↑S : Set ℤ) (fun _ => ENNReal.ofReal ε₁) k)
      = (M : ℝ≥0∞) * ENNReal.ofReal ε₁ := by
    rw [tsum_eq_sum (s := S)
      fun k hk => Set.indicator_of_notMem (fun h => hk (Finset.mem_coe.1 h)) _]
    rw [Finset.sum_congr rfl fun k hk => Set.indicator_of_mem (Finset.mem_coe.2 hk) _,
      Finset.sum_const, nsmul_eq_mul]
  have hfarsum : (∑' k : ℤ, Set.indicator ((↑S : Set ℤ)ᶜ)
        (fun k => ENNReal.ofReal (C / a) * cellSup p k) k)
      ≤ ENNReal.ofReal (C / a) * driNorm p := by
    rw [driNorm_def, ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun k => Set.indicator_le_self _ _ k
  calc driNorm (fun x => ‖w x - smoothed w a x‖ₑ)
      ≤ ∑' k : ℤ, (Set.indicator (↑S : Set ℤ) (fun _ => ENNReal.ofReal ε₁) k
          + Set.indicator ((↑S : Set ℤ)ᶜ)
              (fun k => ENNReal.ofReal (C / a) * cellSup p k) k) :=
        ENNReal.tsum_le_tsum hcell
    _ = (∑' k : ℤ, Set.indicator (↑S : Set ℤ) (fun _ => ENNReal.ofReal ε₁) k)
          + ∑' k : ℤ, Set.indicator ((↑S : Set ℤ)ᶜ)
              (fun k => ENNReal.ofReal (C / a) * cellSup p k) k := ENNReal.tsum_add
    _ ≤ (M : ℝ≥0∞) * ENNReal.ofReal ε₁ + ENNReal.ofReal (C / a) * ENNReal.ofReal D := by
        rw [hnear, ← hDeq]; exact add_le_add le_rfl hfarsum
    _ = ENNReal.ofReal ((M : ℝ) * ε₁ + C / a * D) := by
        rw [ENNReal.ofReal_add (mul_nonneg hMcast hε₁0.le)
            (mul_nonneg (div_nonneg hC0 ha.le) hD0),
          ENNReal.ofReal_mul (Nat.cast_nonneg M),
          ENNReal.ofReal_mul (div_nonneg hC0 ha.le), ENNReal.ofReal_natCast]
    _ < ENNReal.ofReal ε := by
        refine (ENNReal.ofReal_lt_ofReal_iff hε).2 ?_
        have h1 : (M : ℝ) * ε₁ < ε / 3 := by
          rw [hε₁def, mul_div_assoc', div_lt_div_iff₀ hden (by norm_num : (0:ℝ) < 3)]
          nlinarith [Nat.cast_nonneg (α := ℝ) M, hε]
        have h2 : C / a * D ≤ ε / 3 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ ha (by norm_num : (0:ℝ) < 3)]
          rw [div_le_iff₀ hε] at haC
          nlinarith [hC0, hD0, ha.le]
        linarith

/-! ### Regularity of the smoothing

The remaining side conditions of `tendsto_of_tendsto_sum_integral_comp_sub_sincSq`.
`Integrable (𝓕 w_a)` is the only one with content, and it is free from the band:
`𝓕w_a` is continuous and vanishes off `[-2a, 2a]`, hence compactly supported. -/

lemma integrable_smoothed {w : ℝ → ℂ} (hw : Integrable w) {a : ℝ} (ha : 0 < a) :
    Integrable (smoothed w a) :=
  hw.integrable_convolution _ (integrable_ofReal_smoothKernel ha)

lemma continuous_smoothed {w : ℝ → ℂ} (hwc : Continuous w) (hws : HasCompactSupport w)
    {a : ℝ} (ha : 0 < a) : Continuous (smoothed w a) :=
  hws.continuous_convolution_left _ hwc (integrable_ofReal_smoothKernel ha).locallyIntegrable

/-- The transform of an `L¹` function is continuous. -/
lemma continuous_fourier_of_integrable {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by exact continuous_inner)
    hf

/-- `𝓕w_a` is integrable because it is *compactly supported*: continuous, and zero
off the band `[-2a, 2a]`. -/
lemma integrable_fourier_smoothed {w : ℝ → ℂ} (hw : Integrable w) {a : ℝ} (ha : 0 < a) :
    Integrable (𝓕 (smoothed w a)) := by
  have hcont : Continuous (𝓕 (smoothed w a)) :=
    continuous_fourier_of_integrable (integrable_smoothed hw ha)
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * a)) (b := 2 * a)) fun ξ hξ => ?_
  refine fourier_smoothed_eq_zero hw ha ?_
  simp only [Set.mem_Icc, not_and_or, not_le] at hξ
  rcases abs_cases ξ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hξ with h | h <;> linarith

/-! ### The transform of the smoothing is Lipschitz at the origin

The last hypothesis of `tendsto_of_tendsto_sum_integral_comp_sub_sincSq` still
open for `w ⋆ K_a`. It is obtained from the two factors of `𝓕(w ⋆ K_a) = 𝓕w·𝓕K_a`
separately, and **that decomposition is not cosmetic**: the elementary bound below
needs `x·w ∈ L¹`, which holds for the compactly supported `w` but *fails* for
`w ⋆ K_a`, whose far field decays only like `x^{-2}`. -/

/-- **`𝓕f` is Lipschitz at the origin with constant `2π‖x·f‖_{L¹}`.**

`𝓕f(t) − 𝓕f(0) = ∫ (e^{-2πixt} − 1)f(x)dx` and `‖e^{iθ} − 1‖ ≤ |θ|`
(`Real.norm_exp_I_mul_ofReal_sub_one_le`), so the whole estimate is one
domination — no differentiation under the integral sign, and in particular no
smoothness of `f`. The price is the first-moment hypothesis. -/
theorem norm_fourier_sub_fourier_zero_le {w : ℝ → ℂ} (hw : Integrable w)
    (hxw : Integrable (fun x : ℝ => (x : ℂ) * w x)) (t : ℝ) :
    ‖𝓕 w t - 𝓕 w 0‖ ≤ (2 * Real.pi * ∫ x : ℝ, ‖(x : ℂ) * w x‖) * |t| := by
  have hmeas : AEStronglyMeasurable
      (fun v : ℝ => Complex.exp (((-2 * Real.pi * (inner ℝ v t) : ℝ) : ℂ) * Complex.I) • w v)
      volume := by
    simp only [smul_eq_mul]
    exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul hw.1
  have hint1 : Integrable
      (fun v : ℝ => Complex.exp (((-2 * Real.pi * (inner ℝ v t) : ℝ) : ℂ) * Complex.I) • w v) := by
    refine Integrable.mono' hw.norm hmeas (Filter.Eventually.of_forall fun v => ?_)
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hb : ∀ v : ℝ,
      ‖Complex.exp (((-2 * Real.pi * (inner ℝ v t) : ℝ) : ℂ) * Complex.I) • w v - w v‖
        ≤ 2 * Real.pi * |t| * ‖(v : ℂ) * w v‖ := by
    intro v
    have hz : Complex.exp (((-2 * Real.pi * (inner ℝ v t) : ℝ) : ℂ) * Complex.I) • w v - w v
        = (Complex.exp (((-2 * Real.pi * (inner ℝ v t) : ℝ) : ℂ) * Complex.I) - 1) * w v := by
      rw [smul_eq_mul]; ring
    have hexp : ‖Complex.exp (((-2 * Real.pi * (inner ℝ v t) : ℝ) : ℂ) * Complex.I) - 1‖
        ≤ 2 * Real.pi * |v| * |t| := by
      have h1 : ‖Complex.exp (((-2 * Real.pi * (inner ℝ v t) : ℝ) : ℂ) * Complex.I) - 1‖
          ≤ |(-2 * Real.pi * (inner ℝ v t) : ℝ)| := by
        rw [mul_comm]
        simpa using Real.norm_exp_I_mul_ofReal_sub_one_le (x := (-2 * Real.pi * (inner ℝ v t) : ℝ))
      refine h1.trans (le_of_eq ?_)
      simp only [RCLike.inner_apply, conj_trivial]
      rw [abs_mul, abs_mul, abs_neg, abs_mul, abs_of_pos Real.pi_pos]
      norm_num
      ring
    rw [hz, norm_mul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖Complex.exp (((-2 * Real.pi * (inner ℝ v t) : ℝ) : ℂ) * Complex.I) - 1‖ * ‖w v‖
        ≤ (2 * Real.pi * |v| * |t|) * ‖w v‖ := mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
      _ = 2 * Real.pi * |t| * (|v| * ‖w v‖) := by ring
  rw [Real.fourier_eq', fourier_zero_eq_integral, ← integral_sub hint1 hw]
  refine le_trans (norm_integral_le_of_norm_le (hxw.norm.const_mul _)
    (Filter.Eventually.of_forall hb)) ?_
  rw [integral_const_mul]
  exact le_of_eq (by ring)

/-- `‖𝓕f‖_∞ ≤ ‖f‖_{L¹}`, the Riemann–Lebesgue-free half of the transform's
boundedness. -/
lemma norm_fourier_le_integral_norm {w : ℝ → ℂ} (hw : Integrable w) (t : ℝ) :
    ‖𝓕 w t‖ ≤ ∫ x : ℝ, ‖w x‖ := by
  rw [Real.fourier_eq']
  refine norm_integral_le_of_norm_le hw.norm (Filter.Eventually.of_forall fun v => ?_)
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- **The transform of the smoothing is Lipschitz at the origin** (4c).

Splitting `𝓕w_a(t) − 𝓕w_a(0) = 𝓕w(t)(𝓕K_a(t) − 𝓕K_a(0)) + (𝓕w(t) − 𝓕w(0))𝓕K_a(0)`
puts each factor where its own estimate lives: the first uses `𝓕K_a`'s Lipschitz
constant `1/(2a)` against `‖𝓕w‖_∞ ≤ ‖w‖_{L¹}`, the second uses `w`'s first moment
against `𝓕K_a(0) = 1`.

This is the last hypothesis of
`tendsto_of_tendsto_sum_integral_comp_sub_sincSq` outstanding for the smoothing. -/
theorem norm_fourier_smoothed_sub_le {w : ℝ → ℂ} (hw : Integrable w)
    (hxw : Integrable (fun x : ℝ => (x : ℂ) * w x)) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    ‖𝓕 (smoothed w a) t - 𝓕 (smoothed w a) 0‖
      ≤ ((∫ x : ℝ, ‖w x‖) * (1 / (2 * a)) + 2 * Real.pi * ∫ x : ℝ, ‖(x : ℂ) * w x‖) * |t| := by
  have hfac : ∀ ξ : ℝ, 𝓕 (smoothed w a) ξ
      = 𝓕 w ξ * 𝓕 (fun u : ℝ => ((smoothKernel a u : ℝ) : ℂ)) ξ := fun ξ => by
    rw [smoothed, Real.fourier_mul_convolution_eq hw (integrable_ofReal_smoothKernel ha) ξ]
  have hG0norm : ‖𝓕 (fun u : ℝ => ((smoothKernel a u : ℝ) : ℂ)) 0‖ = 1 := by
    rw [fourier_ofReal_smoothKernel_zero ha, norm_one]
  have hsplit : 𝓕 (smoothed w a) t - 𝓕 (smoothed w a) 0
      = 𝓕 w t * (𝓕 (fun u : ℝ => ((smoothKernel a u : ℝ) : ℂ)) t
            - 𝓕 (fun u : ℝ => ((smoothKernel a u : ℝ) : ℂ)) 0)
        + (𝓕 w t - 𝓕 w 0) * 𝓕 (fun u : ℝ => ((smoothKernel a u : ℝ) : ℂ)) 0 := by
    rw [hfac t, hfac 0]; ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_mul, hG0norm, mul_one]
  have h1 : ‖𝓕 w t‖ * ‖𝓕 (fun u : ℝ => ((smoothKernel a u : ℝ) : ℂ)) t
        - 𝓕 (fun u : ℝ => ((smoothKernel a u : ℝ) : ℂ)) 0‖
      ≤ (∫ x : ℝ, ‖w x‖) * (1 / (2 * a) * |t|) :=
    mul_le_mul (norm_fourier_le_integral_norm hw t)
      (norm_fourier_ofReal_smoothKernel_sub_le ha t) (norm_nonneg _)
      (integral_nonneg fun _ => norm_nonneg _)
  have h2 := norm_fourier_sub_fourier_zero_le hw hxw t
  calc ‖𝓕 w t‖ * ‖𝓕 (fun u : ℝ => ((smoothKernel a u : ℝ) : ℂ)) t
          - 𝓕 (fun u : ℝ => ((smoothKernel a u : ℝ) : ℂ)) 0‖ + ‖𝓕 w t - 𝓕 w 0‖
      ≤ (∫ x : ℝ, ‖w x‖) * (1 / (2 * a) * |t|)
          + (2 * Real.pi * ∫ x : ℝ, ‖(x : ℂ) * w x‖) * |t| := add_le_add h1 h2
    _ = ((∫ x : ℝ, ‖w x‖) * (1 / (2 * a))
          + 2 * Real.pi * ∫ x : ℝ, ‖(x : ℂ) * w x‖) * |t| := by ring

/-! ### The renewal limit at a smoothing

Every hypothesis of `tendsto_of_tendsto_sum_integral_comp_sub_sincSq` is now
available for `w ⋆ K_a`, so the bandlimited renewal limit applies to it verbatim.
This is the approximant whose limit the general d.R.i. statement is squeezed
onto. -/

theorem tendsto_tsum_integral_comp_sub_smoothed {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {C : ℝ≥0∞} (hC : ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + 1)) ≤ C) (hCfin : C ≠ ∞)
    {w : ℝ → ℂ} (hwc : Continuous w) (hws : HasCompactSupport w) {a : ℝ} (ha : 0 < a)
    (hdri : driNorm (fun x => ‖smoothed w a x‖ₑ) ≠ ∞) :
    Filter.Tendsto (fun y : ℝ => ∑' n, ∫ s, smoothed w a (y - s) ∂(convPow μ n))
      Filter.atTop (nhds ((∫ x : ℝ, smoothed w a x) / ((∫ x, x ∂μ : ℝ) : ℂ))) := by
  have hwi : Integrable w := hwc.integrable_of_hasCompactSupport hws
  have hxws : HasCompactSupport (fun x : ℝ => (x : ℂ) * w x) := hws.mul_left
  have hxw : Integrable (fun x : ℝ => (x : ℂ) * w x) :=
    (Complex.continuous_ofReal.mul hwc).integrable_of_hasCompactSupport hxws
  have h1 : (0 : ℝ) ≤ ∫ x : ℝ, ‖w x‖ := integral_nonneg fun _ => norm_nonneg _
  have h2 : (0 : ℝ) ≤ ∫ x : ℝ, ‖(x : ℂ) * w x‖ := integral_nonneg fun _ => norm_nonneg _
  refine tendsto_of_tendsto_sum_integral_comp_sub_sincSq hμ hint hm
    (continuous_smoothed hwc hws ha) (integrable_smoothed hwi ha)
    (integrable_fourier_smoothed hwi ha)
    (fun t ht => fourier_smoothed_eq_zero hwi ha ht)
    (norm_fourier_smoothed_sub_le hwi hxw ha) ?_ ?_
  · have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    exact add_nonneg (mul_nonneg h1 (by positivity)) (mul_nonneg hpi h2)
  · exact fun y => (summable_integral_comp_sub_of_driNorm hC hCfin hdri y).hasSum.tendsto_sum_nat

/-! ### The key renewal theorem

Everything meets here. `z` is approximated in `‖·‖_DRI` by a cutoff and then a
smoothing; the smoothing is bandlimited, so its renewal limit is known; and the
d.R.i. error estimate moves both the series and its target by at most a multiple
of the approximation error, uniformly in `y`. -/

/-- **The key renewal theorem for continuous directly Riemann integrable kernels**
(A-5c), the input the paper's `lem:nd-gaussian-renewal` needs:

  `∑ₙ ∫ z(y−s) μ^{*n}(ds) ⟶ (∫z)/m̂`  as `y → ∞`.

The hypotheses are the chapter's: `μ` nonlattice with a second moment and positive
drift, plus a finite exponential moment `∫e^{-θz}dμ < 1` — supplied by the Cramér
tilt — which is what makes the cell bound two-sided.

**Deviation from the paper**, deliberate and recorded: the paper routes through
Feller's interval theorem and assumes only that `z` is *a.e.* continuous, whereas
this proof approximates in `‖·‖_DRI` and needs `z` continuous. Indicators are not
`‖·‖_DRI`-approximable by continuous functions, so the gap is real; it is
acceptable here because the chapter's forcing is Gaussian-driven, hence atomless,
hence continuous — an obligation to discharge at the instantiation. -/
theorem tendsto_tsum_integral_comp_sub_of_driNorm {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {θ : ℝ} (hθ : 0 < θ) (hlt : expTransform θ μ < 1)
    {z : ℝ → ℂ} (hzc : Continuous z) (hz : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) :
    Filter.Tendsto (fun y : ℝ => ∑' n, ∫ s, z (y - s) ∂(convPow μ n))
      Filter.atTop (nhds ((∫ x : ℝ, z x) / ((∫ x, x ∂μ : ℝ) : ℂ))) := by
  -- the uniform cell bound, with a nonnegative constant
  obtain ⟨C₀, hC₀⟩ := exists_bound_renewalMeasure_Icc_of_expTransform hμ hint hm hθ hlt 1
  set K : ℝ := max C₀ 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hC : ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + 1)) ≤ ENNReal.ofReal K := fun y =>
    (hC₀ y).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hCfin : ENNReal.ofReal K ≠ ∞ := ENNReal.ofReal_ne_top
  have hzi : Integrable z := integrable_of_driNorm hzc hz
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- the d.R.i. accuracy that buys `ε/2` in both the series and its target
  set δ : ℝ := ε / (2 * (K + (∫ x, x ∂μ)⁻¹ + 1)) with hδdef
  have hmpos : 0 < (∫ x, x ∂μ)⁻¹ := inv_pos.2 hm
  have hden : 0 < 2 * (K + (∫ x, x ∂μ)⁻¹ + 1) := by linarith
  have hδ : 0 < δ := div_pos hε hden
  -- approximate: cutoff, then smoothing
  obtain ⟨w, hwc, hws, -, hzw⟩ :=
    exists_hasCompactSupport_driNorm_sub_lt hzc hz
      (ENNReal.ofReal_pos.2 (half_pos hδ))
  obtain ⟨a, ha, hwv⟩ := exists_driNorm_smoothed_sub_lt hwc hws (half_pos hδ)
  set v : ℝ → ℂ := smoothed w a with hvdef
  have hvc : Continuous v := continuous_smoothed hwc hws ha
  -- the total approximation error
  have hzv : driNorm (fun x => ‖z x - v x‖ₑ) < ENNReal.ofReal δ := by
    refine lt_of_le_of_lt (driNorm_enorm_sub_le_add z w v) ?_
    calc driNorm (fun x => ‖z x - w x‖ₑ) + driNorm (fun x => ‖w x - v x‖ₑ)
        < ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
          ENNReal.add_lt_add hzw hwv
      _ = ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
          norm_num
  have hzvfin : driNorm (fun x => ‖z x - v x‖ₑ) ≠ ∞ := hzv.ne_top
  have hvfin : driNorm (fun x => ‖v x‖ₑ) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hz, hzvfin⟩) (driNorm_enorm_le_add_sub z v)
  have hvi : Integrable v := integrable_of_driNorm hvc hvfin
  -- the error in the series, uniformly in `y`
  have hser : ∀ y : ℝ, ‖(∑' n, ∫ s, z (y - s) ∂(convPow μ n))
      - ∑' n, ∫ s, v (y - s) ∂(convPow μ n)‖
        ≤ (ENNReal.ofReal K * driNorm (fun x => ‖z x - v x‖ₑ)).toReal := fun y =>
    norm_tsum_integral_comp_sub_sub_le hC hCfin hzc hvc hz hvfin hzvfin y
  have hbound1 : (ENNReal.ofReal K * driNorm (fun x => ‖z x - v x‖ₑ)).toReal ≤ K * δ := by
    have hle : ENNReal.ofReal K * driNorm (fun x => ‖z x - v x‖ₑ)
        ≤ ENNReal.ofReal (K * δ) := by
      rw [ENNReal.ofReal_mul hK0]
      gcongr
    calc (ENNReal.ofReal K * driNorm (fun x => ‖z x - v x‖ₑ)).toReal
        ≤ (ENNReal.ofReal (K * δ)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = K * δ := ENNReal.toReal_ofReal (by positivity)
  -- the error in the target
  have hint2 : ‖(∫ x : ℝ, z x) - ∫ x : ℝ, v x‖ ≤ δ := by
    refine (norm_integral_sub_le_driNorm hzi hvi hzvfin).trans ?_
    calc (driNorm (fun x => ‖z x - v x‖ₑ)).toReal
        ≤ (ENNReal.ofReal δ).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hzv.le
      _ = δ := ENNReal.toReal_ofReal hδ.le
  have hmne : (∫ x, x ∂μ) ≠ 0 := ne_of_gt hm
  have htarget : ‖(∫ x : ℝ, v x) / ((∫ x, x ∂μ : ℝ) : ℂ)
      - (∫ x : ℝ, z x) / ((∫ x, x ∂μ : ℝ) : ℂ)‖ ≤ (∫ x, x ∂μ)⁻¹ * δ := by
    rw [div_sub_div_same, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm,
      div_le_iff₀ hm, norm_sub_rev]
    calc ‖(∫ x : ℝ, z x) - ∫ x : ℝ, v x‖ ≤ δ := hint2
      _ = (∫ x, x ∂μ)⁻¹ * δ * (∫ x, x ∂μ) := by field_simp
  -- the smoothing's own limit
  have hlim := tendsto_tsum_integral_comp_sub_smoothed hμ hint hm hC hCfin hwc hws ha hvfin
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨Y, hY⟩ := hlim (ε / 2) (half_pos hε)
  refine ⟨Y, fun y hy => ?_⟩
  have hnear := hY y hy
  rw [dist_eq_norm] at hnear ⊢
  set A : ℂ := ∑' n, ∫ s, z (y - s) ∂(convPow μ n) with hAdef
  set B : ℂ := ∑' n, ∫ s, v (y - s) ∂(convPow μ n) with hBdef
  set P : ℂ := (∫ x : ℝ, v x) / ((∫ x, x ∂μ : ℝ) : ℂ) with hPdef
  set Q : ℂ := (∫ x : ℝ, z x) / ((∫ x, x ∂μ : ℝ) : ℂ) with hQdef
  have hδeq : δ * (2 * (K + (∫ x, x ∂μ)⁻¹ + 1)) = ε := by rw [hδdef]; field_simp
  calc ‖A - Q‖ = ‖(A - B) + ((B - P) + (P - Q))‖ := by congr 1; ring
    _ ≤ ‖A - B‖ + ‖(B - P) + (P - Q)‖ := norm_add_le _ _
    _ ≤ ‖A - B‖ + (‖B - P‖ + ‖P - Q‖) := by gcongr; exact norm_add_le _ _
    _ ≤ K * δ + (ε / 2 + (∫ x, x ∂μ)⁻¹ * δ) :=
        add_le_add ((hser y).trans hbound1) (add_le_add hnear.le htarget)
    _ < ε := by nlinarith [hδ, hK0, hmpos.le]

/-- **The key renewal theorem for real-valued kernels** (A-6b). Same statement as
`tendsto_tsum_integral_comp_sub_of_driNorm`, for `z : ℝ → ℝ`:

  `∑ₙ ∫ z(y−s) μ^{*n}(ds) ⟶ (∫z)/m̂`  as `y → ∞`.

The complex form is the one the Fourier argument produces, but the chapter's
forcing `Ψ_y(1)` is real, so this is the shape `lem:nd-gaussian-renewal`
consumes. The transport is purely formal: `Complex.ofReal` is a continuous ring
embedding, it commutes with `∫` (`integral_complex_ofReal`) and with `∑'`
(`Complex.ofReal_tsum`, which needs no summability hypothesis because both sides
degenerate to `0` together), and it reflects limits
(`Filter.tendsto_ofReal_iff`). The d.R.i. hypothesis is literally the same, since
`‖(x : ℂ)‖ = |x|`.

The continuity deviation recorded on the complex version applies verbatim. -/
theorem tendsto_tsum_integral_comp_sub_of_driNorm_real_jb247_oai {μ : Measure ℝ}
    [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {θ : ℝ} (hθ : 0 < θ) (hlt : expTransform θ μ < 1)
    {z : ℝ → ℝ} (hzc : Continuous z) (hz : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) :
    Filter.Tendsto (fun y : ℝ => ∑' n, ∫ s, z (y - s) ∂(convPow μ n))
      Filter.atTop (nhds ((∫ x : ℝ, z x) / (∫ x, x ∂μ))) := by
  have hz' : driNorm (fun x => ‖((z x : ℝ) : ℂ)‖ₑ) ≠ ∞ := by
    simpa [enorm_eq_nnnorm] using hz
  have h := tendsto_tsum_integral_comp_sub_of_driNorm hμ hint hm hθ hlt
    (z := fun x => ((z x : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hzc) hz'
  have hlim : ((∫ x : ℝ, ((z x : ℝ) : ℂ)) / ((∫ x, x ∂μ : ℝ) : ℂ))
      = (((∫ x : ℝ, z x) / (∫ x, x ∂μ) : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, ← Complex.ofReal_div]
  rw [hlim] at h
  rw [← Filter.tendsto_ofReal_iff]
  refine h.congr fun y => ?_
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun n => integral_complex_ofReal

end Renewal

end AbsorptionCutoff
end

theorem solution : type_of% @AbsorptionCutoff.Renewal.tendsto_tsum_integral_comp_sub_of_driNorm_real_jb247_oai := @AbsorptionCutoff.Renewal.tendsto_tsum_integral_comp_sub_of_driNorm_real_jb247_oai
