-- Prove2me | Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
-- name    : LeanLevy_RandomMeasure_PoissonRandomMeasure
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T22:26:10.903949+00:00
-- url     : https://prove2.me/theorems/ed507fc7-79eb-42a1-947b-92a1943a06ca
-- title:
--   LeanLevy source module: RandomMeasure.PoissonRandomMeasure
-- statement:
--   Source-faithful definition and structural-lemma bundle for `LeanLevy.RandomMeasure.PoissonRandomMeasure`. It preserves the original Lean declarations, namespaces, assumptions and imported definitions. The upstream source is credited below. This is a draft pending Prove2Me compilation.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonRandomMeasure.lean

/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily

/-!
# The Poisson random measure

Given a Poisson point family `IsPoissonPointFamily K X m μ` for a σ-finite intensity `m` on `E`
(a count `K k` and points `X k n` on each finite-mass partition piece, all jointly independent), the
**Poisson random measure** places a unit atom at each realized point:
`poissonRandomMeasure K X ω = ∑ₖ ∑_{n < K k ω} δ_{X k n ω}`. This file constructs it as a genuine
`Measure E`-valued random object — not an axiomatized one — and identifies the laws of its set
evaluations.

## Main definitions

* `ProbabilityTheory.poissonRandomMeasure` — the random measure itself, a `Measure E` for each `ω`.

## Main results

* `ProbabilityTheory.poissonRandomMeasure_apply` — the evaluation on a measurable set `A` is the total
  number of realized points landing in `A`, `∑ₖ thinnedCount K X A k`.
* `ProbabilityTheory.measurable_poissonRandomMeasure_apply` — that evaluation is a measurable function
  of `ω`.
* `ProbabilityTheory.map_poissonRandomMeasure_apply` — **superposition**: the count of points in a
  finite-mass set `A` is Poisson-distributed with mean `m A`.
* `ProbabilityTheory.ae_poissonRandomMeasure_apply_lt_top` — the count in a finite-mass set is almost
  surely finite.
* `ProbabilityTheory.integrable_toReal_poissonRandomMeasure_apply` — the `ℝ`-valued count in a
  finite-mass set is integrable.
* `ProbabilityTheory.integral_toReal_poissonRandomMeasure_apply` — the `ℝ`-valued count in a
  finite-mass set has mean `(m A).toReal`.
* `ProbabilityTheory.indepFun_poissonRandomMeasure_apply` — the counts in two disjoint finite-mass
  sets are independent (the two-set API).
* `ProbabilityTheory.iIndepFun_poissonRandomMeasure_apply` — **mutual independence**: the counts in a
  finite pairwise-disjoint family of finite-mass sets are mutually independent.
* `ProbabilityTheory.tsum_measure_prmPiece_inter` — the per-piece intensities of a measurable set sum
  to its total mass, `∑ₖ m (piece k ∩ A) = m A`.
* `ProbabilityTheory.lintegral_poissonRandomMeasure_apply` — the evaluation on a measurable set `A`
  has `ℝ≥0∞`-mean equal to the intensity `m A` (both sides may be `⊤`).
* `ProbabilityTheory.lintegral_poissonRandomMeasure` — the Lebesgue integral of a measurable `g`
  against the random measure is the sum of `g` over the realized points.
* `ProbabilityTheory.lintegral_lintegral_poissonRandomMeasure` — **Campbell's formula**: the mean of
  `∫⁻ g dN` over `ω` is `∫⁻ g dm`.

The evaluation laws are read off the thinning and within-piece factorization of
`PoissonPointFamily` by superposing the independent pieces: the count in `A` is the sum of the
per-piece thinned counts, whose partial sums are Poisson by convolution and whose independence across
pieces comes from the prefix-versus-next-block splitting of the point family.
-/

open MeasureTheory Filter Complex
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
  {m : Measure E} [SigmaFinite m] [Nonempty E] {μ : Measure Ω} {A B : Set E} {k : ℕ} {ω : Ω}

/-- **The Poisson random measure** of a Poisson point family: for each `ω`, the measure placing a
unit Dirac mass at each of the realized points `X k n ω` (for `n < K k ω`) across all pieces `k`.
Equivalently `∑ₖ ∑_{n < K k ω} δ_{X k n ω}`. -/
noncomputable def poissonRandomMeasure (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E) (ω : Ω) : Measure E :=
  Measure.sum fun k => Measure.sum fun n =>
    if n < K k ω then Measure.dirac (X k n ω) else 0

omit [MeasurableSpace E] [MeasurableSpace Ω] [Nonempty E] in
/-- The `ℝ≥0∞`-cast of the thinned count as a finite sum of point-membership indicators. -/
private lemma thinnedCount_toENNReal :
    (thinnedCount K X A k ω : ℝ≥0∞)
      = ∑ n ∈ Finset.range (K k ω), A.indicator (1 : E → ℝ≥0∞) (X k n ω) := by
  classical
  rw [thinnedCount, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hx : X k n ω ∈ A
  · rw [Set.indicator_of_mem hx, if_pos hx, Pi.one_apply, Nat.cast_one]
  · rw [Set.indicator_of_notMem hx, if_neg hx, Nat.cast_zero]

omit [MeasurableSpace Ω] [Nonempty E] in
/-- **Evaluation of the Poisson random measure.** On a measurable set `A`, the random measure counts
the total number of realized points across all pieces landing in `A`. -/
theorem poissonRandomMeasure_apply (hA : MeasurableSet A) :
    poissonRandomMeasure K X ω A = ∑' k, (thinnedCount K X A k ω : ℝ≥0∞) := by
  classical
  rw [poissonRandomMeasure, Measure.sum_apply _ hA]
  refine tsum_congr fun k => ?_
  rw [Measure.sum_apply _ hA]
  have hterm : ∀ n, (if n < K k ω then Measure.dirac (X k n ω) else 0) A
      = if n < K k ω then A.indicator (1 : E → ℝ≥0∞) (X k n ω) else 0 := by
    intro n
    rw [apply_ite (fun ν : Measure E => ν A), Measure.dirac_apply' _ hA, Measure.coe_zero,
      Pi.zero_apply]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Finset.range (K k ω)) fun n hn => by
    rw [if_neg (by simpa [Finset.mem_range] using hn)]]
  rw [thinnedCount_toENNReal]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [if_pos (by simpa [Finset.mem_range] using hn)]

omit [Nonempty E] in
/-- The set evaluation of the Poisson random measure is a measurable function of `ω`. -/
theorem measurable_poissonRandomMeasure_apply (hK : ∀ k, Measurable (K k))
    (hX : ∀ k n, Measurable (X k n)) (hA : MeasurableSet A) :
    Measurable fun ω => poissonRandomMeasure K X ω A := by
  simp_rw [poissonRandomMeasure_apply hA]
  refine Measurable.tsum fun k => ?_
  exact measurable_from_top.comp (measurable_thinnedCount (hK k) (hX k) hA)

/-! ### Superposition: the law of the count in a set

The count of realized points in a measurable set `A` is the superposition `∑ₖ thinnedCount K X A k`
of the per-piece thinned counts. Its partial sums `prmPartialCount K X A n` are Poisson-distributed
(by convolution, using the prefix-versus-next-block independence of the point family), and passing to
the limit — legitimate because the total count is almost surely finite, with `E[count] = m A < ⊤` —
identifies the count in `A` as Poisson with mean `m A`. -/

omit [Nonempty E] in
/-- The rates of the per-piece thinned counts sum to the total mass: `∑ₖ m (piece k ∩ A) = m A`,
since the pieces intersected with `A` partition `A`. -/
theorem tsum_measure_prmPiece_inter (hA : MeasurableSet A) :
    ∑' k, m (prmPiece m k ∩ A) = m A := by
  rw [← measure_iUnion (fun i j hij =>
        (pairwise_disjoint_prmPiece hij).mono Set.inter_subset_left Set.inter_subset_left)
      (fun k => measurableSet_prmPiece.inter hA),
    ← Set.iUnion_inter, iUnion_prmPiece, Set.univ_inter]

/-- The `ℝ≥0∞`-mean of `poissonMeasure r` is `r`. -/
private lemma lintegral_id_poissonMeasure (r : ℝ≥0) :
    ∫⁻ n, (n : ℝ≥0∞) ∂(poissonMeasure r) = (r : ℝ≥0∞) := by
  rw [lintegral_countable' (fun n : ℕ => (n : ℝ≥0∞))]
  have hsingle : ∀ n : ℕ, poissonMeasure r {n} = ENNReal.ofReal ((poissonMeasure r).real {n}) := by
    intro n
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hterm : ∀ n : ℕ, (n : ℝ≥0∞) * poissonMeasure r {n}
      = ENNReal.ofReal ((n : ℝ) * (poissonMeasure r).real {n}) := by
    intro n
    rw [hsingle, ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg (Nat.cast_nonneg n) measureReal_nonneg)
      (poissonExpectation_hasSum r).summable, (poissonExpectation_hasSum r).tsum_eq,
    ENNReal.ofReal_coe_nnreal]

/-- The `ℝ≥0∞`-mean of the thinned count is the mass of the piece intersected with `A`. -/
private lemma lintegral_thinnedCount [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hA : MeasurableSet A) :
    ∫⁻ ω, (thinnedCount K X A k ω : ℝ≥0∞) ∂μ = m (prmPiece m k ∩ A) := by
  have hTA : Measurable (thinnedCount K X A k) :=
    measurable_thinnedCount (hd.measurable_count k) (hd.measurable_point k) hA
  have hmap : ∫⁻ ω, (thinnedCount K X A k ω : ℝ≥0∞) ∂μ
      = ∫⁻ n : ℕ, (n : ℝ≥0∞) ∂(μ.map (thinnedCount K X A k)) :=
    (lintegral_map (f := fun n : ℕ => (n : ℝ≥0∞)) measurable_from_top hTA).symm
  rw [hmap, map_thinnedCount hd hA, lintegral_id_poissonMeasure,
    ENNReal.coe_toNNReal (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
      measure_prmPiece_lt_top).ne]

/-- **Evaluation mean of the Poisson random measure.** The total count in a measurable set `A` has
`ℝ≥0∞`-mean equal to the intensity `m A` (both sides may be `⊤`). -/
theorem lintegral_poissonRandomMeasure_apply [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) :
    ∫⁻ ω, poissonRandomMeasure K X ω A ∂μ = m A := by
  simp_rw [poissonRandomMeasure_apply hA]
  rw [lintegral_tsum (f := fun k ω => (thinnedCount K X A k ω : ℝ≥0∞)) fun k =>
    (measurable_from_top.comp
      (measurable_thinnedCount (hd.measurable_count k) (hd.measurable_point k) hA)).aemeasurable]
  simp_rw [lintegral_thinnedCount hd hA]
  exact tsum_measure_prmPiece_inter hA

/-- The total count in a finite-mass set is almost surely finite. -/
theorem ae_poissonRandomMeasure_apply_lt_top [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hfin : m A < ⊤) :
    ∀ᵐ ω ∂μ, poissonRandomMeasure K X ω A < ⊤ :=
  ae_lt_top (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hA)
    (by rw [lintegral_poissonRandomMeasure_apply hd hA]; exact hfin.ne)

/-- **The partial superposition count**: the number of realized points landing in `A` coming from the
first `n + 1` pieces. Its `n → ∞` limit is the total count in `A`. -/
private noncomputable def prmPartialCount (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E) (A : Set E) (n : ℕ)
    (ω : Ω) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), thinnedCount K X A k ω











/-! ### The superposition law: the count in a finite-mass set is Poisson

The partial counts `prmPartialCount K X A n` increase to the total count `poissonRandomMeasure K X · A`
almost surely (the total count being finite by `ae_poissonRandomMeasure_apply_lt_top`), so their
Poisson laws pass to the limit. The identification is carried out through characteristic functions and
dominated convergence: the characteristic function of each partial count is the Poisson pgf with the
accumulated rate `∑_{k ≤ n} m (piece k ∩ A)`, and these rates increase to `m A`. -/

















/-! ### Pairwise independence of the counts in disjoint sets

For two disjoint finite-mass sets `A` and `B`, the counts `poissonRandomMeasure K X · A` and
`poissonRandomMeasure K X · B` are independent. The proof is the joint analogue of the superposition
law: the pair of partial counts `(prmPartialCount A n, prmPartialCount B n)` has a joint
characteristic function that factorizes — each piece contributes an independent pair (the
prefix-versus-next-block splitting), and within each piece the two counts are independent because `A`
and `B` are disjoint (`indepFun_thinnedCount_thinnedCount`, packaged in `charFunDual_prod_thinnedCount`).
Passing to the limit by dominated convergence identifies the joint characteristic function of the pair
`(count A, count B)` as a product, hence independence. This two-set statement is retained as API;
mutual independence over a finite pairwise-disjoint family is delivered below by
`iIndepFun_poissonRandomMeasure_apply`. -/

















/-! ### Mutual independence of the counts in a finite disjoint family

The pairwise statement above upgrades verbatim to a finite family `A : ι → Set E` of pairwise disjoint
finite-mass sets: the counts `poissonRandomMeasure K X · (A i)` are **mutually** independent. The proof
is the `ι`-indexed mirror of the pairwise chain — the pair `(A, B)` is replaced by the family `A`, the
codomain `ℝ × ℝ` by `ι → ℝ`, and the two-set factorizations by the joint pgf identity
`charFunDual_pi_thinnedCount` (PoissonPointFamily). The joint characteristic function of the partial-count vector
factorizes across coordinates (by induction on the number of pieces), passes to the limit by dominated
convergence, and identifies the joint characteristic function of the count vector as a product; the
mathlib vehicle `iIndepFun_iff_charFunDual_pi` then delivers mutual independence. -/











/-! ### Lebesgue integration against the random measure

The Lebesgue integral of a measurable `g : E → ℝ≥0∞` against `poissonRandomMeasure K X ω` collapses
to the sum of `g` over the realized points, and **Campbell's formula** identifies its mean over `ω`
with `∫⁻ g dm`. The mean is proved by monotone simple-function approximation, reducing to the
evaluation mean `lintegral_poissonRandomMeasure_apply` on each fiber of an approximant. -/









end ProbabilityTheory


