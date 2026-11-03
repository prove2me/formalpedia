-- Prove2me | Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
-- name    : LeanLevy_RandomMeasure_TimeSpacePoisson
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T22:27:06.44851+00:00
-- url     : https://prove2.me/theorems/7545ab9c-7da0-4ecb-8b6d-7218804209ad
-- title:
--   LeanLevy source module: RandomMeasure.TimeSpacePoisson
-- statement:
--   Source-faithful definition and structural-lemma bundle for `LeanLevy.RandomMeasure.TimeSpacePoisson`. It preserves the original Lean declarations, namespaces, assumptions and imported definitions. The upstream source is credited below. This is a draft pending Prove2Me compilation.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/TimeSpacePoisson.lean

/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral

/-!
# Time-indexed Poisson random measures

Specialize the abstract Poisson random measure to the product space `ℝ × E`, with `ℝ` read as time
and `E` as the mark space, under the product intensity `volume.prod m`. The evaluation on a
space-time band `(s, t] × A` is the number of realized marks in `A` occurring during the time
window `(s, t]`; the running count `poissonTimeCount K X A t` is its value on the initial window
`(0, t]`.

## Main definitions

* `ProbabilityTheory.poissonTimeCount` — the running count of realized points in `(0, t] × A`.
* `ProbabilityTheory.levyCompensatedSmallJump` — the compensated small-jump integral of a Lévy
  measure at time `t`, as an element of `L²(μ)`.

## Main results

* `ProbabilityTheory.measurable_poissonTimeCount` — the running count is a measurable function of the
  sample point.
* `ProbabilityTheory.map_poissonRandomMeasure_band` — the count in a band `(s, t] × A` is Poisson with
  mean `(t - s) · m A`.
* `ProbabilityTheory.map_poissonTimeCount` — the running count `poissonTimeCount K X A t` is Poisson
  with mean `t · m A`.
* `ProbabilityTheory.poissonTimeCount_add` — the running count is pathwise additive over consecutive
  time windows.
* `ProbabilityTheory.iIndepFun_poissonRandomMeasure_bands` — **independent increments**: the counts
  over consecutive disjoint time bands are mutually independent.
* `ProbabilityTheory.memLp_two_smallJumpFun` — the small-jump test function is square-integrable
  against `volume.prod ν` for any Lévy measure `ν`.
* `ProbabilityTheory.memLp_two_smallJumpBandFun` — the same for the band test function supported on a
  time window `(s, t]`.
* `ProbabilityTheory.levyCompensatedSmallJump_sub` — the increment of the compensated small-jump
  integral over `(s, t]` is the compensated integral of the band test function.
* `ProbabilityTheory.integral_levyCompensatedSmallJump` — the compensated small-jump integral has
  mean zero.
* `ProbabilityTheory.eLpNorm_sq_levyCompensatedSmallJump` — **Campbell's isometry**: its second
  moment is `t · ∫_{(-1,1)} x² dν`.
* `ProbabilityTheory.map_levyLargeJumpCount` — the number of large jumps up to time `t` is Poisson
  with mean `t · ν {x | 1 ≤ |x|}`.
* `ProbabilityTheory.levyLargeJumpSum` — the sum of the jump sizes of the realized marks in the band
  `(0, t] × {x | 1 ≤ |x|}`, as a series of piece sums.
* `ProbabilityTheory.measurable_levyLargeJumpSum` — the large-jump sum is a measurable function of the
  sample point.
* `ProbabilityTheory.levyLargeJumpSum_ae_eq_integral` — almost surely the large-jump sum is the
  Bochner integral of the jump size against the random measure over the band.
* `ProbabilityTheory.integral_levyLargeJumpSum` — **Campbell's formula**: under a first moment on the
  large jumps, the mean of the large-jump sum is `t · ∫_{|x|≥1} x dν`.
* `ProbabilityTheory.levyLargeJumpSum_ae_eq_toReal_sub` — the large-jump sum as a difference of
  Lebesgue integrals of the positive and negative jump parts.
* `ProbabilityTheory.charFun_map_levyLargeJumpSum` — **the large-jump sum is compound Poisson**: its
  characteristic function is `exp (t · ∫_{|x|≥1} (e^{iξx} − 1) dν)`.
* `ProbabilityTheory.charFun_map_compensatedBandSum` — the compensated Poisson sum of the band test
  function on a mark set `A ⊆ (-1, 1)` of finite `ν`-mass has characteristic function
  `exp (t · ∫_A (e^{ixξ} − 1 − ixξ) dν)`.
* `ProbabilityTheory.charFun_map_levyCompensatedSmallJump` — **the law of the compensated small-jump
  integral**: its characteristic function is `exp (t · ∫_{(-1,1)} (e^{ixξ} − 1 − ixξ) dν)`, the
  small-jump factor of the Lévy–Khintchine exponent.
* `ProbabilityTheory.charFun_map_levyLargeJumpSum_sub`,
  `ProbabilityTheory.charFun_map_levyCompensatedSmallJump_sub` — **the increment laws over a time band
  `(s, t]`**: the large-jump increment is compound Poisson and the compensated small-jump increment
  carries the small-jump factor, both at rate `(t − s)`.

Every statement is read off the abstract superposition and disjoint-family independence laws of
`poissonRandomMeasure` on `ℝ × E`; the band mass factorizes as `volume (Ioc s t) * m A` through
`Measure.prod_prod`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω] [Nonempty E] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × E} {m : Measure E} [SigmaFinite m] {μ : Measure Ω} {A : Set E} {s t : ℝ}

omit [Nonempty E] in
/-- The `volume.prod m`-mass of a space-time band factorizes: `(volume.prod m) ((s, t] ×ˢ A)` is the
time length `t - s` times the mark mass `m A`. -/
theorem volume_prod_Ioc_prod (s t : ℝ) (A : Set E) :
    (volume.prod m) (Set.Ioc s t ×ˢ A) = ENNReal.ofReal (t - s) * m A := by
  rw [Measure.prod_prod, Real.volume_Ioc]

omit [Nonempty E] in
/-- Each space-time band has finite `volume.prod m`-mass whenever the mark set has finite mass. -/
theorem volume_prod_Ioc_prod_lt_top (hfin : m A < ⊤) :
    (volume.prod m) (Set.Ioc s t ×ˢ A) < ⊤ := by
  rw [volume_prod_Ioc_prod]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-- The running count of points of the time-space random measure: realized points in `(0, t] × A`. -/
noncomputable def poissonTimeCount (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × E)
    (A : Set E) (t : ℝ) (ω : Ω) : ℝ≥0∞ :=
  poissonRandomMeasure K X ω (Set.Ioc 0 t ×ˢ A)













/-! ### The compensated small-jump integral of a Lévy measure

Specializing the mark space to `E = ℝ` and the intensity to `volume.prod ν` for a **Lévy measure**
`ν`, the small-jump test function `1_{(0,t] × (-1,1)}(s, x) · x` is square-integrable, so its
compensated Poisson integral `levyCompensatedSmallJump` is a genuine `L²(μ)` random variable. It
has mean zero and second moment `t · ∫_{(-1,1)} x² dν` (Campbell's isometry). The number of large
jumps up to time `t` is Poisson with mean `t · ν {|x| ≥ 1}`. -/

section LevyIntensity

variable {ν : Measure ℝ} [SigmaFinite ν] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {μ : Measure Ω}



omit [SigmaFinite ν] in
/-- The pointwise square of a band indicator over a measurable mark set integrates to the set
lintegral of `x²`. -/
private lemma lintegral_enorm_rpow_band {B : Set ℝ} (hB : MeasurableSet B) (s t : ℝ) :
    ∫⁻ p, ‖(Set.Ioc s t ×ˢ B).indicator (fun q : ℝ × ℝ => q.2) p‖ₑ ^ (2 : ℝ)
        ∂(volume.prod ν)
      = ∫⁻ p in Set.Ioc s t ×ˢ B, ENNReal.ofReal (p.2 ^ 2) ∂(volume.prod ν) := by
  rw [← lintegral_indicator (measurableSet_Ioc.prod hB)]
  refine lintegral_congr fun p => ?_
  by_cases hp : p ∈ Set.Ioc s t ×ˢ B
  · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, sq_abs]
  · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, enorm_zero,
      ENNReal.zero_rpow_of_pos (by norm_num)]

/-- Tonelli for a band over a measurable mark set: `∫_{(s,t]×B} x² = (t - s) · ∫_B x²`. -/
private lemma setLIntegral_band_snd_sq {B : Set ℝ} (_hB : MeasurableSet B) (s t : ℝ) :
    ∫⁻ p in Set.Ioc s t ×ˢ B, ENNReal.ofReal (p.2 ^ 2) ∂(volume.prod ν)
      = ENNReal.ofReal (t - s) * ∫⁻ x in B, ENNReal.ofReal (x ^ 2) ∂ν := by
  rw [← Measure.prod_restrict,
    lintegral_prod (fun p : ℝ × ℝ => ENNReal.ofReal (p.2 ^ 2))
      (measurable_snd.pow_const 2).ennreal_ofReal.aemeasurable]
  have hinner : ∀ r : ℝ,
      ∫⁻ x, ENNReal.ofReal ((r, x).2 ^ 2) ∂(ν.restrict B)
        = ∫⁻ x in B, ENNReal.ofReal (x ^ 2) ∂ν := fun _ => rfl
  rw [lintegral_congr hinner, setLIntegral_const, Real.volume_Ioc, mul_comm]

omit [SigmaFinite ν] in
/-- The set-lintegral of `x²` over `(-1,1)` against a Lévy measure is finite. -/
private lemma lintegral_Ioo_sq_lt_top (hν : IsLevyMeasure ν) :
    ∫⁻ x in Set.Ioo (-1) 1, ENNReal.ofReal (x ^ 2) ∂ν < ⊤ := by
  refine lt_of_le_of_lt ?_ hν.2
  rw [← lintegral_indicator measurableSet_Ioo]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ Set.Ioo (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hx]
    obtain ⟨h1, h2⟩ := hx
    exact ENNReal.ofReal_le_ofReal (le_min (by nlinarith) le_rfl)
  · rw [Set.indicator_of_notMem hx]; exact zero_le

/-- The small-jump band test function `1_{(s,t] × (-1,1)}(u, x) · x` is square-integrable against
`volume.prod ν` for any Lévy measure `ν`. -/
theorem memLp_two_smallJumpBandFun (hν : IsLevyMeasure ν) (s t : ℝ) :
    MemLp ((Set.Ioc s t ×ˢ Set.Ioo (-1) 1).indicator fun p : ℝ × ℝ => p.2) 2 (volume.prod ν) := by
  refine ⟨(measurable_snd.indicator
    (measurableSet_Ioc.prod measurableSet_Ioo)).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) from by norm_num]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  rw [lintegral_enorm_rpow_band measurableSet_Ioo s t, setLIntegral_band_snd_sq measurableSet_Ioo s t]
  exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_Ioo_sq_lt_top hν)).ne

/-- The small-jump test function `1_{(0,t] × (-1,1)}(u, x) · x` is square-integrable against
`volume.prod ν` for any Lévy measure `ν`. -/
theorem memLp_two_smallJumpFun (hν : IsLevyMeasure ν) (t : ℝ) :
    MemLp ((Set.Ioc 0 t ×ˢ Set.Ioo (-1) 1).indicator fun p : ℝ × ℝ => p.2) 2 (volume.prod ν) :=
  memLp_two_smallJumpBandFun hν 0 t

/-- The compensated small-jump integral of a Lévy measure at time `t`, as an element of `L²(μ)`. -/
noncomputable def levyCompensatedSmallJump [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) (hν : IsLevyMeasure ν) (t : ℝ) :
    Lp ℝ 2 μ :=
  compensatedPoissonIntegral hd ((memLp_two_smallJumpFun hν t).toLp _)











/-! ### The large-jump sum process

The **large-jump sum** `levyLargeJumpSum` is the sum of the jump sizes of the realized marks in the
band `(0, t] × {x | 1 ≤ |x|}`, written as a series of piece sums. Almost surely only finitely many
marks land in the band (their count is a.s. finite), so the defining series is a.s. a finite sum. It
agrees a.s. with the Bochner integral of the jump size against the random measure over the band and
splits into positive and negative Lebesgue parts. Under a first moment on the large jumps its mean is
`t · ∫_{|x|≥1} x dν` (Campbell's formula). -/















/-- The **large-jump sum**: the sum of the jump sizes of the realized marks in
`(0, t] × {x | 1 ≤ |x|}`, as a series of piece sums. Almost surely this is a finite sum. -/
noncomputable def levyLargeJumpSum (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∑' k, pieceSum K X
    ((Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω











/-! ### The compound-Poisson characteristic function of the large-jump sum

The characteristic function of the large-jump sum is the compound-Poisson exponential
`exp (t · ∫_{|x|≥1} (e^{iξx} − 1) dν)`. The proof runs through the piece decomposition: each piece
contributes a probability-generating factor `exp (∫_{piece} (e^{iξx} − 1) d(volume.prod ν))`
(`integral_exp_pieceSum`), the finitely-many-piece partial products factorize by prefix-versus-block
independence (`charFun_partial_largeJumpSum`), and dominated convergence together with the
piece-partition sum of the band integral pass to the limit. -/





















/-! ### The characteristic function of compensated band sums

For a mark set `A ⊆ (-1, 1)` with finite `ν`-mass, the compensated Poisson sum of the band test
function `1_{(0,t] × A}(u, x) · x` has characteristic function
`exp (t · ∫_A (e^{ixξ} − 1 − ixξ) dν)`. The proof is the sibling of `charFun_map_levyLargeJumpSum`
with the per-piece compensator riding along: the compensated partial sums factor into per-piece
factors carrying the extra `−iξ ∫ f` drift, and dominated convergence together with the
piece-partition sum of the band integral pass to the limit. -/





/-- The band test function lies in `L²(volume.prod ν)` when `A ⊆ (-1, 1)` has finite mass: its
square is bounded by `1` on the finite-mass support. -/
lemma memLp_two_bandFun {A : Set ℝ} (hA : MeasurableSet A)
    (hAsub : A ⊆ Set.Ioo (-1) 1) (hAfin : ν A < ⊤) (s t : ℝ) :
    MemLp ((Set.Ioc s t ×ˢ A).indicator fun p : ℝ × ℝ => p.2) 2
      ((volume : Measure ℝ).prod ν) := by
  have hbandmeas : MeasurableSet (Set.Ioc s t ×ˢ A) := measurableSet_Ioc.prod hA
  have hbandfin : (volume.prod ν) (Set.Ioc s t ×ˢ A) < ⊤ :=
    volume_prod_Ioc_prod_lt_top (m := ν) (s := s) (t := t) hAfin
  refine ⟨(measurable_snd.indicator hbandmeas).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) from by norm_num]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  have hle : (fun p : ℝ × ℝ =>
        ‖(Set.Ioc s t ×ˢ A).indicator (fun q : ℝ × ℝ => q.2) p‖ₑ ^ (2 : ℝ))
      ≤ (Set.Ioc s t ×ˢ A).indicator fun _ : ℝ × ℝ => (1 : ℝ≥0∞) := by
    intro p
    dsimp only
    by_cases hp : p ∈ Set.Ioc s t ×ˢ A
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
      obtain ⟨h1, h2⟩ := hAsub hp.2
      have habs : |p.2| ≤ 1 := abs_le.mpr ⟨le_of_lt h1, le_of_lt h2⟩
      calc ‖p.2‖ₑ ^ (2 : ℝ) ≤ (1 : ℝ≥0∞) ^ (2 : ℝ) := by
            refine ENNReal.rpow_le_rpow ?_ (by norm_num)
            rw [Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_one.mpr habs
        _ = 1 := ENNReal.one_rpow _
    · rw [Set.indicator_of_notMem hp, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
      exact bot_le
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono hle) ?_)
  rw [lintegral_indicator hbandmeas, setLIntegral_const, one_mul]
  exact hbandfin







/-! ### The law of the compensated small-jump integral

The compensated small-jump integral `levyCompensatedSmallJump` has characteristic function
`exp (t · ∫_{(-1,1)} (e^{ixξ} − 1 − ixξ) dν)` — the small-jump factor of the Lévy–Khintchine
exponent. The proof truncates the mark set to the annuli `A n := (-1, 1) ∩ {x | 1/(n+1) ≤ |x|}`,
each of finite `ν`-mass, so that `charFun_map_compensatedBandSum` applies to the truncated integral;
the truncated integral converges to `levyCompensatedSmallJump` in `L²(μ)`, hence its characteristic
function converges, and the exponent converges by dominated convergence. -/







omit [SigmaFinite ν] in
/-- As `n → ∞`, the shrinking-ball tail of `∫ x² dν` over `(-1, 1)` vanishes. -/
lemma tendsto_lintegral_slice_sq (hν : IsLevyMeasure ν) :
    Tendsto (fun n : ℕ => ∫⁻ x in Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | |x| < ((n:ℝ) + 1)⁻¹},
        ENNReal.ofReal (x ^ 2) ∂ν) atTop (𝓝 0) := by
  have hslice_meas : ∀ n : ℕ,
      MeasurableSet (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | |x| < ((n:ℝ) + 1)⁻¹}) :=
    fun n => measurableSet_Ioo.inter (measurableSet_lt continuous_abs.measurable measurable_const)
  have hsqmeas : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ 2)) :=
    ENNReal.measurable_ofReal.comp (measurable_id'.pow_const 2)
  have hlim : ∀ x : ℝ, Tendsto (fun n : ℕ =>
      (Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | |y| < ((n:ℝ) + 1)⁻¹}).indicator
        (fun y => ENNReal.ofReal (y ^ 2)) x) atTop (𝓝 0) := by
    intro x
    by_cases hx0 : x = 0
    · have hz : (fun n : ℕ => (Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | |y| < ((n:ℝ) + 1)⁻¹}).indicator
          (fun y => ENNReal.ofReal (y ^ 2)) x) = fun _ => 0 := by
        funext n; simp [Set.indicator_apply, hx0]
      rw [hz]; exact tendsto_const_nhds
    · have habs : (0:ℝ) < |x| := abs_pos.mpr hx0
      obtain ⟨N, hN⟩ := exists_nat_gt (|x|⁻¹)
      have hev : ∀ᶠ (n : ℕ) in atTop, (Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | |y| < ((n:ℝ) + 1)⁻¹}).indicator
          (fun y => ENNReal.ofReal (y ^ 2)) x = 0 := by
        rw [Filter.eventually_atTop]
        refine ⟨N, fun n hn => Set.indicator_of_notMem (fun hmem => ?_) _⟩
        have hxinv : |x|⁻¹ < (n:ℝ) + 1 := by
          have hNn : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
          linarith [hN]
        have h1 : (1:ℝ) < |x| * ((n:ℝ) + 1) := by
          have h2 := mul_lt_mul_of_pos_left hxinv habs
          rwa [mul_inv_cancel₀ (ne_of_gt habs)] at h2
        have hc_lt : ((n:ℝ) + 1)⁻¹ < |x| := by
          rw [inv_eq_one_div, div_lt_iff₀ (Nat.cast_add_one_pos n)]; linarith [h1]
        exact absurd hmem.2 (not_lt.mpr hc_lt.le)
      exact (tendsto_congr' hev).mpr tendsto_const_nhds
  have hdct := tendsto_lintegral_of_dominated_convergence (μ := ν)
    (F := fun n x => (Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | |y| < ((n:ℝ) + 1)⁻¹}).indicator
      (fun y => ENNReal.ofReal (y ^ 2)) x)
    (f := fun _ => 0)
    (bound := (Set.Ioo (-1:ℝ) 1).indicator fun y => ENNReal.ofReal (y ^ 2))
    (fun n => hsqmeas.indicator (hslice_meas n))
    (fun n => Filter.Eventually.of_forall fun x =>
      Set.indicator_le_indicator_apply_of_subset Set.inter_subset_left zero_le)
    (by rw [lintegral_indicator measurableSet_Ioo]; exact (lintegral_Ioo_sq_lt_top hν).ne)
    (Filter.Eventually.of_forall hlim)
  have hrw : (fun n : ℕ => ∫⁻ x,
        (Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | |y| < ((n:ℝ) + 1)⁻¹}).indicator
          (fun y => ENNReal.ofReal (y ^ 2)) x ∂ν)
      = fun n : ℕ => ∫⁻ x in Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | |x| < ((n:ℝ) + 1)⁻¹},
          ENNReal.ofReal (x ^ 2) ∂ν := by
    funext n; rw [lintegral_indicator (hslice_meas n)]
  rw [hrw] at hdct
  simpa using hdct









end LevyIntensity

end ProbabilityTheory


