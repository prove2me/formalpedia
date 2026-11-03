-- Prove2me | Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
-- name    : LeanLevy_RandomMeasure_LevyJumpPath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-31T10:26:11.854748+00:00
-- url     : https://prove2.me/theorems/34d08df2-9283-4861-8f01-cad378425a10
-- title:
--   LeanLevy source module: RandomMeasure.LevyJumpPath
-- statement:
--   Pinned source definition and helper bundle. The original generated Lean module passed the earlier local build. This draft awaits Prove2Me remote compilation.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpPath.lean

/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Pathwise banded jump sums

For a mark set `A ⊆ ℝ`, the **banded jump sum** `bandJumpSum K X A t ω` accumulates the marks of the
realized points that fall in the space-time window `(0, t] × A`, written as a series of piece sums.
It generalizes the large-jump sum `levyLargeJumpSum` (the mark set `{x | 1 ≤ |x|}`) to an arbitrary
band.

When the band has finite `ν`-mass, only finitely many pieces are active in any bounded time window
`(0, T]`, so almost surely each sample path `t ↦ bandJumpSum K X A t ω` agrees on `(-∞, T)` with a
finite sum of right-continuous jump steps. Such finite step sums are càdlàg, hence so is the sample
path. This gives the sample-path regularity of the large-jump component of a Lévy process.

For a band `A ⊆ (-1, 1)` of finite `ν`-mass, the compensated **banded jump path**
`levyBandPath K X ν A t ω = bandJumpSum K X A t ω - t · ∫_A x dν` subtracts the linear compensator
drift. Almost surely it agrees with the compensated Poisson integral of the band test function
`1_{(0,t] × A}(u, x) · x`, so it lies in `L²(μ)`, is càdlàg, and — through a
`prmFiltration`-adapted representative `levyBandVersion` — is a martingale for the natural filtration.

## Main definitions

* `ProbabilityTheory.bandJumpSum` — the sum of the marks of the realized points in the window
  `(0, t] × A`, as a series of piece sums.
* `ProbabilityTheory.levyBandPath` — the compensated banded jump path
  `bandJumpSum K X A t ω - t · ∫_A x dν`.
* `ProbabilityTheory.levyBandVersion` — a `prmFiltration`-adapted representative of the compensated
  band integral.
* `ProbabilityTheory.levyAnnulus` — the annulus `(-1, 1) ∩ {1/(n+1) ≤ |x|}`; the annuli exhaust the
  punctured small-jump band.
* `ProbabilityTheory.levyTruncationSeq` — the geometric truncation subsequence of annulus indices
  along which the tail second moments decay like `16⁻ʲ`.
* `ProbabilityTheory.levySmallJumpGoodSet` — the measurable, almost-sure event carrying full pathwise
  control of the annulus paths.
* `ProbabilityTheory.levySmallJumpPath` — the compensated small-jump path, the almost-sure uniform
  limit of the compensated banded jump paths over the growing annuli (gated to the good set).
* `ProbabilityTheory.levyJumpPath` — the càdlàg pure-jump process indexed by `ℝ≥0`: drift plus
  large-jump sum plus the compensated small-jump path. It shares its drift and large-jump summands
  literally with `levyJumpProcess`, differing only in the (a.e.-equal) small-jump summand, and so
  realizes the same law while carrying a.e.-càdlàg sample paths.

## Main results

* `ProbabilityTheory.exists_isLevyProcess_pureJump` — **the headline**: every pure-jump Lévy triple
  `(b, 0, ν)` is realized by a genuine `IsLevyProcess` — a probability space and a process with
  literal zero start, a.e. càdlàg paths, independent and stationary increments, measurable
  time-slices, and marginal characteristic functions `exp (t · ψ_{(b,0,ν)})`.
* `ProbabilityTheory.bandJumpSum_zero` — the banded jump sum vanishes at time zero.
* `ProbabilityTheory.levyLargeJumpSum_eq_bandJumpSum` — the large-jump sum is the banded jump sum on
  the mark set `{x | 1 ≤ |x|}`.
* `ProbabilityTheory.measurable_bandJumpSum` — the banded jump sum is a measurable function of the
  sample point.
* `ProbabilityTheory.ae_isCadlag_bandJumpSum` — for a band of finite `ν`-mass, almost every sample
  path `t ↦ bandJumpSum K X A t ω` is càdlàg (a.e. in `ω`, for every `t`).
* `ProbabilityTheory.ae_isCadlag_levyLargeJumpSum` — almost every sample path of the large-jump sum
  `t ↦ levyLargeJumpSum K X t ω` is càdlàg.
* `ProbabilityTheory.levyBandPath_ae_eq_compensated` — the compensated band path agrees almost
  everywhere with the compensated Poisson integral of the band test function.
* `ProbabilityTheory.martingale_levyBandVersion` — the adapted representative of the compensated band
  integral is a martingale for the natural filtration `prmFiltration`.
* `ProbabilityTheory.measure_countable_sup_levyBandPath_ge` — the weak-type maximal inequality for the
  compensated band path over a countable time grid: the measure of the event that the path exceeds `ε`
  in absolute value at some grid time is at most `√(T · ∫_A x² dν) / ε`.
* `ProbabilityTheory.levyTruncationSeq_spec` — the truncation subsequence is strictly monotone with
  geometrically-decaying (`16⁻ʲ`) tail second moments.
* `ProbabilityTheory.measurableSet_levySmallJumpGoodSet`, `ae_mem_levySmallJumpGoodSet` — the good set
  is measurable and almost sure.
* `ProbabilityTheory.tendsto_levyBandPath_levySmallJumpPath` — on the good set and for `t ≥ 0`, the
  annulus paths converge to the compensated small-jump path.
* `ProbabilityTheory.isCadlag_levySmallJumpPath` — for *every* `ω`, the compensated small-jump path is
  càdlàg (unconditional through the off-good-set-zero gating).
* `ProbabilityTheory.measurable_levySmallJumpPath` — the compensated small-jump path is measurable at
  each time.
* `ProbabilityTheory.levySmallJumpPath_ae_eq` — for each fixed `t ≥ 0`, the compensated small-jump
  path agrees `μ`-almost everywhere with the `L²` small-jump element `levyCompensatedSmallJump`
  (a per-time modification statement; the null set may depend on `t`).
* `ProbabilityTheory.levyJumpPath_zero` — the jump path vanishes at time zero (literal function
  equality `= fun _ => 0`).
* `ProbabilityTheory.measurable_levyJumpPath` — the jump path is measurable at each time.
* `ProbabilityTheory.levyJumpPath_ae_eq` — at each fixed time the jump path agrees `μ`-almost
  everywhere with the law-level jump process `levyJumpProcess` (they differ only in the small-jump
  summand, which is a per-time modification of the other).
* `ProbabilityTheory.ae_isCadlag_levyJumpPath` — almost every sample path `t ↦ levyJumpPath t ω` is
  càdlàg (a.e. in `ω`).
* `ProbabilityTheory.isLevyProcess_levyJumpPath` — the jump path is a genuine `IsLevyProcess` for the
  pure-jump triple `(b, 0, ν)`: literal zero start, a.e. càdlàg paths, independent and stationary
  increments.
* `ProbabilityTheory.charFun_map_levyJumpPath` — the fixed-time marginal law of the jump path has
  characteristic function `exp (t · ψ_{(b,0,ν)})`.
* `ProbabilityTheory.charExponent_levyJumpPath` — the characteristic exponent of the jump path is the
  Lévy–Khintchine exponent `ψ_{(b,0,ν)}` of the pure-jump triple.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ}
  {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω} {A : Set ℝ}

/-- The **banded jump sum**: the sum of the marks of the realized points in the space-time window
`(0, t] × A`, as a series of piece sums. Almost surely, when `A` has finite `ν`-mass, this is a
finite sum. -/
noncomputable def bandJumpSum (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × ℝ) (A : Set ℝ)
    (t : ℝ) (ω : Ω) : ℝ :=
  ∑' k, pieceSum K X ((Set.Ioc 0 t ×ˢ A).indicator fun p => p.2) k ω







/-! ### Sample-path regularity

On a bounded time window `(0, T]` only finitely many pieces carry a realized mark in `A` (when `A`
has finite `ν`-mass), so the banded jump sum agrees on `(-∞, T)` with a finite sum of right-continuous
jump steps. The step sum is càdlàg by `IsCadlag.finsetSum` and `isCadlag_stepIndicator`, and càdlàg
regularity passes to the banded jump sum by locality of the càdlàg property. -/

/-- The finite step-sum path over an active-piece set `S`: for each realized point `(k, n)` with
`k ∈ S`, a right-continuous jump of size `p.2` triggered at the point's time coordinate `p.1`, active
only for points with positive time and mark in `A`. This is the finite càdlàg comparison path for
`bandJumpSum` on a bounded time window. -/
private noncomputable def bandStepFinsetSum (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × ℝ)
    (A : Set ℝ) (ω : Ω) (S : Finset ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ S, ∑ n ∈ Finset.range (K k ω),
    (if (X k n ω).1 ≤ t then
      ({p : ℝ × ℝ | 0 < p.1 ∧ p.2 ∈ A}).indicator (fun p : ℝ × ℝ => p.2) (X k n ω) else 0)









/-! ### The compensated banded jump path

Subtracting the linear compensator drift `t · ∫_A x dν` from the banded jump sum yields the
**compensated banded jump path** `levyBandPath`. For a band `A ⊆ (-1, 1)` of finite `ν`-mass it agrees
almost everywhere with the compensated Poisson integral of the band test function
`1_{(0,t] × A}(u, x) · x`, hence is square-integrable, càdlàg, and martingale-structured. -/

/-- The **compensated banded jump path**: the banded jump sum with its linear compensator drift
`t · ∫_A x dν` subtracted, so that (for a band of finite `ν`-mass) it has mean zero at each time. -/
noncomputable def levyBandPath (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × ℝ) (ν : Measure ℝ)
    (A : Set ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  bandJumpSum K X A t ω - t * ∫ x in A, x ∂ν









/-! ### The compensated band martingale

For a band `A ⊆ (-1, 1)` of finite `ν`-mass the compensated band integral (an element of `L²(μ)`) is
a martingale for the natural filtration `prmFiltration`. The increment over a time step `(s, t]` is
the compensated Poisson integral of the band test function `1_{(s,t] × A}(r, x) · x`, supported in the
disjoint band region `(s, t] × ℝ`; hence it is independent of the prefix `(-∞, s] × ℝ` and has mean
zero, so its conditional expectation given the past vanishes. -/

/-- The band test function `1_{(s,t] × A}(r, x) · x`, viewed in `L²`, vanishes almost everywhere
outside any product region `B ×ˢ univ` whose time factor contains `(s, t]`. -/
private lemma bandFun_toLp_ae_zero_off (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1)
    (hAfin : ν A < ⊤) {s t : ℝ} {B : Set ℝ} (hB : Set.Ioc s t ⊆ B) :
    ∀ᵐ p ∂((volume : Measure ℝ).prod ν), p ∉ B ×ˢ (Set.univ : Set ℝ) →
      (memLp_two_bandFun hA hAsub hAfin s t).toLp
          ((Set.Ioc s t ×ˢ A).indicator fun q : ℝ × ℝ => q.2) p = 0 := by
  filter_upwards [MemLp.coeFn_toLp (memLp_two_bandFun hA hAsub hAfin s t)] with p hp hpB
  rw [hp]
  apply Set.indicator_of_notMem
  intro hmem
  exact hpB ⟨hB hmem.1, Set.mem_univ _⟩

/-- The compensated band integral over `(0, t]` is almost-everywhere strongly measurable with respect
to the evaluation sigma-algebra of the prefix region `(-∞, t] × ℝ`. -/
private lemma aestronglyMeasurable_levyBandPath_prefix [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤) (t : ℝ≥0) :
    AEStronglyMeasurable[prmEvalSigma K X (volume.prod ν) (Set.Iic (t : ℝ) ×ˢ Set.univ)]
      (compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin 0 (t : ℝ)).toLp _)) μ :=
  aestronglyMeasurable_compensatedPoissonIntegral_prmEvalSigma hd
    (measurableSet_Iic.prod MeasurableSet.univ)
    (bandFun_toLp_ae_zero_off hA hAsub hAfin Set.Ioc_subset_Iic_self)





/-- A `prmFiltration`-adapted representative of the compensated band integral over `(0, t]`. -/
noncomputable def levyBandVersion [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (_hν : IsLevyMeasure ν)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤) (t : ℝ≥0) : Ω → ℝ :=
  (aestronglyMeasurable_levyBandPath_prefix hd hA hAsub hAfin t).mk _









/-! ### Maximal inequality over a countable grid

For a band `A ⊆ (-1, 1)` of finite `ν`-mass the compensated band path satisfies a weak-type maximal
inequality (a Doob-style bound via the elementary maximal inequality `maximal_ineq`): the measure of
the event that the path exceeds a level `ε` in absolute value at some time in a countable subset of
`[0, T]` is bounded by `√(T · ∫_A x² dν) / ε`. The proof restricts the `ℝ≥0`-indexed band martingale
to a monotone `ℕ`-grid, applies the finite maximal inequality to each finite sub-grid, and passes to
the countable limit through continuity of measure from below. -/







/-- The `ℕ`-grid filtration obtained by restricting `prmFiltration` along a monotone reindexing. -/
private noncomputable def gridFiltration
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω› where
  seq k := prmFiltration K X ν hd.measurable_count hd.measurable_point (u k)
  mono' _ _ hij := (prmFiltration K X ν hd.measurable_count hd.measurable_point).mono (hu hij)
  le' k := (prmFiltration K X ν hd.measurable_count hd.measurable_point).le (u k)











/-! ### The truncation subsequence

The compensated small-jump path is built as the uniform limit of the compensated banded jump paths
over the growing **annuli** `levyAnnulus n = (-1, 1) ∩ {1/(n+1) ≤ |x|}`, which exhaust the punctured
band `(-1, 1) \ {0}`. Since `∫_{(-1,1)} x² dν < ∞`, the tail second moment over
`(-1, 1) \ levyAnnulus n` vanishes as `n → ∞`; extracting a geometrically-fast subsequence
`levyTruncationSeq` makes the increments between successive annuli summable in `L²`, which (through the
maximal inequality) drives the almost-sure uniform convergence. -/

/-- The **annulus** `(-1, 1) ∩ {1/(n+1) ≤ |x|}`: the small-jump band with a hole of radius `1/(n+1)`
excised around the origin. The annuli grow with `n` and exhaust the punctured band `(-1, 1) \ {0}`. -/
noncomputable def levyAnnulus (n : ℕ) : Set ℝ :=
  Set.Ioo (-1 : ℝ) 1 ∩ {x : ℝ | ((n : ℝ) + 1)⁻¹ ≤ |x|}

/-- The annulus is contained in the small-jump band `(-1, 1)`. -/
lemma levyAnnulus_subset (n : ℕ) : levyAnnulus n ⊆ Set.Ioo (-1 : ℝ) 1 :=
  Set.inter_subset_left

/-- The annulus is measurable. -/
lemma measurableSet_levyAnnulus (n : ℕ) : MeasurableSet (levyAnnulus n) :=
  measurableSet_Ioo.inter (measurableSet_le measurable_const continuous_abs.measurable)



omit [SigmaFinite ν] in
/-- The annulus has finite `ν`-mass for any Lévy measure `ν`. -/
lemma levyAnnulus_finite_mass (hν : IsLevyMeasure ν) (n : ℕ) : ν (levyAnnulus n) < ⊤ :=
  (measure_mono Set.inter_subset_right).trans_lt
    (hν.measure_setOf_abs_ge_lt_top (by positivity))

omit [SigmaFinite ν] in
/-- The band complement `(-1, 1) \ levyAnnulus n` is exactly the shrinking central slice
`(-1, 1) ∩ {|x| < 1/(n+1)}`. -/
lemma Ioo_diff_levyAnnulus (n : ℕ) :
    Set.Ioo (-1 : ℝ) 1 \ levyAnnulus n
      = Set.Ioo (-1 : ℝ) 1 ∩ {x : ℝ | |x| < ((n : ℝ) + 1)⁻¹} := by
  ext x
  simp only [levyAnnulus, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_setOf_eq, not_and, not_le]
  constructor
  · rintro ⟨hxIoo, h⟩; exact ⟨hxIoo, h hxIoo⟩
  · rintro ⟨hxIoo, h⟩; exact ⟨hxIoo, fun _ => h⟩

omit [SigmaFinite ν] in
/-- From the vanishing tail moments, for any starting index `N` and any positive tolerance `16⁻ʲ`,
some later annulus index `n > N` has tail second moment below the tolerance. -/
private lemma exists_gt_lintegral_Ioo_diff_levyAnnulus_le (hν : IsLevyMeasure ν) (N j : ℕ) :
    ∃ n, N < n ∧ (∫⁻ x in Set.Ioo (-1 : ℝ) 1 \ levyAnnulus n,
        ENNReal.ofReal (x ^ 2) ∂ν) ≤ (16 : ℝ≥0∞)⁻¹ ^ j := by
  have hc : (0 : ℝ≥0∞) < (16 : ℝ≥0∞)⁻¹ ^ j :=
    ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) j
  have htendsto : Tendsto (fun n : ℕ => ∫⁻ x in Set.Ioo (-1 : ℝ) 1 \ levyAnnulus n,
      ENNReal.ofReal (x ^ 2) ∂ν) atTop (𝓝 0) := by
    simpa only [Ioo_diff_levyAnnulus] using tendsto_lintegral_slice_sq hν
  have hev := (htendsto.eventually (Iio_mem_nhds hc)).and (eventually_gt_atTop N)
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨n, hn.2, hn.1.le⟩

/-- The recursively-defined geometric truncation subsequence: each index is chosen strictly larger
than the previous one so that the tail second moment over `(-1, 1) \ levyAnnulus` drops below
`16⁻ʲ`. -/
private noncomputable def levyTruncationAux (hν : IsLevyMeasure ν) : ℕ → ℕ
  | 0 => (exists_gt_lintegral_Ioo_diff_levyAnnulus_le hν 0 0).choose
  | (j + 1) =>
      (exists_gt_lintegral_Ioo_diff_levyAnnulus_le hν (levyTruncationAux hν j) (j + 1)).choose

omit [SigmaFinite ν] in
private lemma levyTruncationAux_lt_succ (hν : IsLevyMeasure ν) (j : ℕ) :
    levyTruncationAux hν j < levyTruncationAux hν (j + 1) :=
  (exists_gt_lintegral_Ioo_diff_levyAnnulus_le hν (levyTruncationAux hν j) (j + 1)).choose_spec.1

omit [SigmaFinite ν] in
private lemma levyTruncationAux_lintegral_le (hν : IsLevyMeasure ν) (j : ℕ) :
    (∫⁻ x in Set.Ioo (-1 : ℝ) 1 \ levyAnnulus (levyTruncationAux hν j),
        ENNReal.ofReal (x ^ 2) ∂ν) ≤ (16 : ℝ≥0∞)⁻¹ ^ j := by
  cases j with
  | zero => exact (exists_gt_lintegral_Ioo_diff_levyAnnulus_le hν 0 0).choose_spec.2
  | succ j =>
      exact (exists_gt_lintegral_Ioo_diff_levyAnnulus_le hν
        (levyTruncationAux hν j) (j + 1)).choose_spec.2

omit [SigmaFinite ν] in
private lemma exists_levyTruncationSeq (hν : IsLevyMeasure ν) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ j : ℕ, (∫⁻ x in Set.Ioo (-1 : ℝ) 1 \ levyAnnulus (φ j),
        ENNReal.ofReal (x ^ 2) ∂ν) ≤ (16 : ℝ≥0∞)⁻¹ ^ j :=
  ⟨levyTruncationAux hν, strictMono_nat_of_lt_succ (levyTruncationAux_lt_succ hν),
    levyTruncationAux_lintegral_le hν⟩

/-- The **geometric truncation subsequence**: a strictly increasing sequence of annulus indices along
which the tail second moment over `(-1, 1) \ levyAnnulus` decays at least geometrically at rate
`16⁻ʲ`. -/
noncomputable def levyTruncationSeq (hν : IsLevyMeasure ν) : ℕ → ℕ :=
  (exists_levyTruncationSeq hν).choose



/-! ### The consecutive annulus slices

`levySlice hν j` is the annular shell added when passing from `levyAnnulus (levyTruncationSeq hν j)`
to `levyAnnulus (levyTruncationSeq hν (j+1))`. Its `ν`-second moment `∫ x² dν` is bounded by the tail
moment `16⁻ʲ`, which makes the compensated band paths over successive annuli a Cauchy sequence in the
maximal-inequality sense. -/

/-- The consecutive annulus slice added between truncation steps `j` and `j+1`. -/
noncomputable def levySlice (hν : IsLevyMeasure ν) (j : ℕ) : Set ℝ :=
  levyAnnulus (levyTruncationSeq hν (j + 1)) \ levyAnnulus (levyTruncationSeq hν j)















/-! ### The almost-sure good event

The compensated small-jump path is defined only on a measurable **good set** carved out so that every
sample point in it enjoys the pathwise properties needed for uniform convergence: finitely many active
pieces in each bounded window (for both the annuli and the slices, giving càdlàg approximants), and a
Borel–Cantelli tail control of the slice paths over a countable time grid. The good set is the
complement of a measurable hull of the (measure-zero) bad event, so it is measurable, almost sure, and
contained in the raw event of full pathwise control. -/

/-- The countable rational time grid on `[0, T]`, together with the right endpoint `T`. -/
noncomputable def levyGrid (T : ℕ) : Set ℝ :=
  (Set.range ((↑) : ℚ → ℝ) ∩ Set.Icc 0 (T : ℝ)) ∪ {(T : ℝ)}





/-- The **bad grid event** at slice index `j` over the window `[0, T]`: the compensated slice path
exceeds the geometric level `2⁻ʲ` at some grid time. Borel–Cantelli sums these over `j`. -/
noncomputable def levyBadGrid (_hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hν : IsLevyMeasure ν) (T j : ℕ) : Set Ω :=
  {ω | ∃ q ∈ levyGrid T, ((2 : ℝ)⁻¹) ^ j ≤ |levyBandPath K X ν (levySlice hν j) q ω|}





/-- The **raw good event**: full pathwise control at `ω`. Its three clauses are (i) window finiteness
for every annulus, (ii) window finiteness for every slice, (iii) Borel–Cantelli tail control of the
slice paths over each grid. -/
def levySmallJumpRaw (_hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hν : IsLevyMeasure ν) (ω : Ω) : Prop :=
  (∀ T j : ℕ, {k | ∃ n ∈ Finset.range (K k ω),
      X k n ω ∈ Set.Ioc 0 (T : ℝ) ×ˢ levyAnnulus (levyTruncationSeq hν j)}.Finite) ∧
  (∀ T j : ℕ, {k | ∃ n ∈ Finset.range (K k ω),
      X k n ω ∈ Set.Ioc 0 (T : ℝ) ×ˢ levySlice hν j}.Finite) ∧
  (∀ T : ℕ, ∀ᶠ j in atTop, ∀ q ∈ levyGrid T,
      |levyBandPath K X ν (levySlice hν j) q ω| < ((2 : ℝ)⁻¹) ^ j)



/-- The **good set** for the compensated small-jump path: the complement of a measurable hull of the
measure-zero bad event. It is measurable, almost sure, and every point in it satisfies the raw
pathwise-control event. -/
noncomputable def levySmallJumpGoodSet
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν) : Set Ω :=
  (MeasureTheory.toMeasurable μ {ω | ¬ levySmallJumpRaw hd hν ω})ᶜ







/-! ### Pathwise infrastructure on the good set

The following lemmas reconstruct, for a single sample point `ω` in the raw good event, the pathwise
facts that hold almost surely: window-local càdlàg regularity of the banded jump paths, disjoint-union
additivity of the compensated band paths, and the slice-additivity of successive annulus paths. They
feed the telescoping estimate that establishes uniform Cauchyness. -/

























/-! ### The compensated small-jump path

`levySmallJumpPath hd hν t ω` is the almost-sure uniform limit of the compensated banded jump paths
over the growing annuli, gated to the good set (and to `t ≥ 0` via `max t 0`). Off the good set it is
identically `0`; on the good set it is the genuine limit, càdlàg for every `ω`. -/

open scoped Classical in
/-- The **compensated small-jump path**: the gated `atTop` limit of the annulus paths. The `max t 0`
guarantees the negative-time slice is constantly `0` (there the drift lines need not converge). -/
noncomputable def levySmallJumpPath
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (t : ℝ) (ω : Ω) : ℝ :=
  Filter.limUnder Filter.atTop (fun j =>
    if ω ∈ levySmallJumpGoodSet hd hν
    then levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) (max t 0) ω else 0)











/-! ### The limit path is a modification of the small-jump integral

The truncation elements — the compensated Poisson integrals of the band test functions over
`(0, t] × levyAnnulus (levyTruncationSeq hν j)` — converge in `L²(μ)` to the compensated
small-jump integral `levyCompensatedSmallJump hd hν t`: the distance is the complementary-slice
seminorm (`eLpNorm_smallJumpBand_sub_bandFun`), whose square is at most `t · 16⁻ʲ` by the
truncation spec. `L²` convergence upgrades to convergence in measure and hence to almost-everywhere
convergence along a subsequence; along it the pathwise annulus approximants converge to both the
compensated small-jump path (the pointwise limit on the good set) and the `L²` element, so the two
agree almost everywhere at each fixed time `t ≥ 0`. -/

/-- The **truncation element** at annulus step `j`: the compensated Poisson integral of the band
test function over `(0, t] × levyAnnulus (levyTruncationSeq hν j)`, as an element of `L²(μ)`. -/
private noncomputable def levyAnnulusElement [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (t : ℝ) (j : ℕ) : Lp ℝ 2 μ :=
  compensatedPoissonIntegral hd ((memLp_two_bandFun
    (measurableSet_levyAnnulus (levyTruncationSeq hν j))
    (levyAnnulus_subset (levyTruncationSeq hν j))
    (levyAnnulus_finite_mass hν (levyTruncationSeq hν j)) 0 t).toLp _)







/-! ### The càdlàg pure-jump process

Assembling the constant drift, the compound-Poisson large-jump sum, and the compensated small-jump
*path* yields a single process `levyJumpPath` indexed by `ℝ≥0`. It shares its drift and large-jump
summands literally with the law-level `levyJumpProcess`, replacing only the `L²` small-jump element
by the pathwise `levySmallJumpPath` — an a.e.-equal per-time modification. The modification carries
over the entire law-level Lévy structure (independent stationary increments, marginal characteristic
function `exp (t · ψ)`) while adding genuine sample-path regularity: almost every path is càdlàg. The
result is a genuine `IsLevyProcess` for the pure-jump triple `(b, 0, ν)`. -/

/-- The **càdlàg pure-jump process**: drift plus large-jump sum plus the compensated small-jump path,
indexed by `ℝ≥0`. Its drift and large-jump summands are literally those of `levyJumpProcess`; the
small-jump summand is the pathwise `levySmallJumpPath`, an a.e. modification of the `L²` element used
there. Unlike `levyJumpProcess`, this process has almost-surely càdlàg sample paths. -/
noncomputable def levyJumpPath
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (b : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  b * (t : ℝ) + levyLargeJumpSum K X (t : ℝ) ω + levySmallJumpPath hd hν (t : ℝ) ω

















end ProbabilityTheory


