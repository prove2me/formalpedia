-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardSpaceDiscrete_F000
-- name    : LevyStochCalc_Ito_PicardSpaceDiscrete_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:12:22.361789+00:00
-- url     : https://prove2.me/theorems/35c536fc-1a72-4525-ac56-a1f32e952c56
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardSpaceDiscrete
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardSpaceDiscrete. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiContractionTight_F000
import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiContraction_F000
import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiNorm_F000
import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiNorm_F001
import Definitions.Def_LevyStochCalc_Ito_PicardSelfMap_F000
import Definitions.Def_LevyStochCalc_Ito_PicardStepMap_F000
import Definitions.Def_LevyStochCalc_Ito_PicardStepMap_F001
import Definitions.Def_LevyStochCalc_Ito_PicardStochasticLipschitz_F000
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Discrete metric on the space of bounded processes

The constant-zero path map inhabits the space `SBoundedProcess` of L²-sup-bounded adapted
processes, and the discrete distance `dist X Y = if X = Y then 0 else 1` makes that space a
complete metric space: a sequence that is Cauchy at scale `< 1` is eventually constant, hence
convergent. The discrete metric carries no analytic content and is not the `S²` or Bielecki
norm; it only supplies the `MetricSpace`/`CompleteSpace` typeclass arguments of the generic
Banach fixed-point shim, the analytic contraction being carried by the Bielecki β-weighted
pseudo-edist of `Ito/PicardSpaceBieleckiEDist.lean`.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]

/-! ### Nonempty: the constant-zero process witnesses inhabitedness. -/

/-- **Constant-zero `SBoundedProcess`.** The map `X t ω = 0` (the zero
vector in `Fin n → ℝ`) is the canonical witness of `Nonempty
(SBoundedProcess P T)`:

* **Measurability** — `Function.uncurry (fun _ _ => 0) = fun _ => 0` is the
  zero constant, hence trivially measurable (`Measurable.const 0`).
* **Càdlàg paths** — every constant function is continuous, so the
  right-limit `Filter.Tendsto` is `tendsto_const_nhds`; for the left
  limit, the witness `L = 0` makes the left-limit `Filter.Tendsto` also
  `tendsto_const_nhds`.
* **`sup_L2`** — `bieleckiNorm β T 0 = 0 < ⊤` because the integrand
  `(∑ i, ‖0‖²) = 0` makes the inner `∫⁻` and the outer rpow both zero;
  multiplying by `ENNReal.ofReal (exp (-β·t))` and taking the supremum
  over `t ∈ [0, T]` still gives zero, which is `< ⊤`. -/
noncomputable def constantZeroProcess
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (T : ℝ) :
    SBoundedProcess (n := n) P ℱ T where
  X := fun _ _ => 0
  measurable_path := by
    have : Function.uncurry (fun (_ : ℝ) (_ : Ω) => (0 : Fin n → ℝ)) =
        fun _ => 0 := by
      funext p
      simp [Function.uncurry]
    rw [this]
    exact measurable_const
  adapted := by
    intro i t
    simpa using
      (stronglyMeasurable_const :
        StronglyMeasurable[@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance]
          fun _ : Ω × ℝ => (0 : ℝ))
  cadlag_paths := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    intro t
    refine ⟨?_, ?_⟩
    · exact tendsto_const_nhds
    · intro _
      exact ⟨0, tendsto_const_nhds⟩
  sup_L2 := by
    unfold bieleckiNorm
    refine lt_of_le_of_lt ?_ ENNReal.zero_lt_top
    refine iSup_le (fun t => ?_)
    refine iSup_le (fun _ => ?_)
    have h_sum_zero : (fun ω : Ω =>
        (∑ i, (‖(fun _ _ => (0 : Fin n → ℝ)) t ω i‖₊ : ℝ≥0∞) ^ 2)) =
        fun _ => 0 := by
      funext ω
      simp
    rw [h_sum_zero]
    simp
/-- `Nonempty` instance: constant zero process. -/
noncomputable instance instNonemptySBoundedProcess
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ} :
    Nonempty (SBoundedProcess (n := n) P ℱ T) :=
  ⟨constantZeroProcess P ℱ T⟩
/-! ### MetricSpace: discrete metric for typeclass satisfaction.

**Typeclass-placeholder notice:** the metric
installed in this section is the *discrete metric* on `SBoundedProcess`:
`dist X Y = 0 if X = Y, else 1`. This satisfies all `MetricSpace` axioms
mechanically but carries **NO substantive analytical content**: it makes
every fixed-point question on `SBoundedProcess`-with-this-metric trivially
discrete (Cauchy ↔ eventually constant; contractions ↔ identity on the
fixed-point fibre; the unique fixed point is the starting iterate). The
goal of this instance is to discharge the typeclass obligation of the
generic Banach shim `picardFixedPoint`, NOT to deliver mathematics.

The literature Banach work (Bielecki β-weighted L²-sup norm with genuine
contraction at the analytical rate `3 n L² (T+2) / (2β)` for
`β > 3 n L² (T+2) / 2`) is carried by the pseudo-edist `bieleckiNorm` on
path maps: the contraction estimate is `bieleckiNorm_picardSelfMap_diff_le`
(`Ito/PicardContraction.lean`) and the well-posedness theorem is
`exists_jumpDiffusion_unique_of_solvesOn` (`Ito/PicardWellPosed.lean`).
Downstream consumers should treat the discrete-metric `picardFixedPoint`
invocation on `SBoundedProcess` as a typeclass shim only.

This is a genuine metric (separation holds by definition, triangle inequality
holds via case analysis), and is **complete** because every Cauchy sequence
in the discrete metric is eventually constant (Cauchy at scale `< 1` forces
all sufficiently far-out terms to be equal).

The discrete metric is **not** the literature `S²` / Bielecki norm — that
is a pseudometric on `SBoundedProcess` (zero distance iff a.s.-equal,
which is weaker than structure equality). The actual Picard contraction
estimate is developed against the pseudo-edist `bieleckiNorm (X - Y)`
in the `bielecki_*` lemma family and against the genuine metric on
`AEQuot β T`, and is logically independent of which `MetricSpace`
instance lives on the `SBoundedProcess` structure type.
-/

section DiscreteMetric
-- The discrete metric construction below uses `if X = Y then 0 else 1`,
-- which needs `Decidable (X = Y)`. Since `SBoundedProcess` is not decidably
-- equal in general, we `open Classical` for this section so the elaborator
-- pulls in the classical decidability instance. Linter is locally disabled
-- via a `set_option` because the `open Classical` is the simplest tactic
-- to thread classical decidability through every declaration in the section.
set_option linter.style.openClassical false
open Classical

variable {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

/-- The discrete distance on `SBoundedProcess`: zero on the diagonal,
one elsewhere. Uses classical decidability of equality (via the
section-local `open Classical`) to make `if X = Y then 0 else 1`
well-typed without needing a `[DecidableEq]` instance. -/
noncomputable def discreteDist
    (X Y : SBoundedProcess (n := n) P ℱ T) : ℝ :=
  if X = Y then 0 else 1
lemma discreteDist_self (X : SBoundedProcess (n := n) P ℱ T) :
    discreteDist X X = 0 := by
  simp [discreteDist]
lemma discreteDist_comm (X Y : SBoundedProcess (n := n) P ℱ T) :
    discreteDist X Y = discreteDist Y X := by
  unfold discreteDist
  by_cases h : X = Y
  · subst h; rfl
  · have h' : ¬ Y = X := fun heq => h heq.symm
    rw [if_neg h, if_neg h']
lemma discreteDist_triangle (X Y Z : SBoundedProcess (n := n) P ℱ T) :
    discreteDist X Z ≤ discreteDist X Y + discreteDist Y Z := by
  unfold discreteDist
  by_cases hXZ : X = Z
  · -- LHS = 0; RHS ≥ 0.
    rw [if_pos hXZ]
    have h₁ : (0 : ℝ) ≤ (if X = Y then (0 : ℝ) else 1) := by
      split_ifs <;> norm_num
    have h₂ : (0 : ℝ) ≤ (if Y = Z then (0 : ℝ) else 1) := by
      split_ifs <;> norm_num
    linarith
  · -- LHS = 1; need 1 ≤ RHS.
    rw [if_neg hXZ]
    by_cases hXY : X = Y
    · by_cases hYZ : Y = Z
      · exact absurd (hXY.trans hYZ) hXZ
      · rw [if_pos hXY, if_neg hYZ]; linarith
    · rw [if_neg hXY]
      have h₂ : (0 : ℝ) ≤ (if Y = Z then (0 : ℝ) else 1) := by
        split_ifs <;> norm_num
      linarith
lemma discreteDist_eq_zero_iff
    (X Y : SBoundedProcess (n := n) P ℱ T) :
    discreteDist X Y = 0 ↔ X = Y := by
  unfold discreteDist
  by_cases h : X = Y
  · simp [h]
  · rw [if_neg h]
    exact ⟨fun h₀ => by linarith, fun heq => absurd heq h⟩
lemma discreteDist_nonneg (X Y : SBoundedProcess (n := n) P ℱ T) :
    0 ≤ discreteDist X Y := by
  unfold discreteDist
  split_ifs <;> norm_num
/-- **`PseudoMetricSpace` instance via the discrete distance.** -/
noncomputable instance instPseudoMetricSpaceSBoundedProcess :
    PseudoMetricSpace (SBoundedProcess (n := n) P ℱ T) where
  dist := discreteDist
  dist_self := discreteDist_self
  dist_comm := discreteDist_comm
  dist_triangle := discreteDist_triangle
/-- **`MetricSpace` instance via the discrete distance.** Promotes the
pseudo-metric to a genuine metric by adding the separation axiom
`dist X Y = 0 → X = Y`, which holds for the discrete distance by
construction. -/
noncomputable instance instMetricSpaceSBoundedProcess :
    MetricSpace (SBoundedProcess (n := n) P ℱ T) where
  __ := instPseudoMetricSpaceSBoundedProcess
  eq_of_dist_eq_zero {X Y} h := (discreteDist_eq_zero_iff X Y).mp h
/-! ### CompleteSpace: every Cauchy sequence in the discrete metric is
eventually constant, hence converges. -/

/-- **Cauchy sequence in the discrete metric is eventually constant.** If
`u : ℕ → SBoundedProcess` is Cauchy with respect to the discrete distance
inherited from `instMetricSpaceSBoundedProcess`, then there exists `N`
such that `u n = u N` for all `n ≥ N`. The witness `N` is obtained from
the Cauchy property at scale `ε = 1/2`: any two terms `u m`, `u n` with
`m, n ≥ N` have `dist (u m) (u n) < 1`, hence by the discrete distance
must satisfy `u m = u n`. -/
lemma cauchySeq_eventually_constant
    (u : ℕ → SBoundedProcess (n := n) P ℱ T) (hu : CauchySeq u) :
    ∃ N : ℕ, ∀ n ≥ N, u n = u N := by
  rw [Metric.cauchySeq_iff] at hu
  obtain ⟨N, hN⟩ := hu (1/2) (by norm_num)
  refine ⟨N, ?_⟩
  intro n hn
  have h_dist : dist (u n) (u N) < 1/2 := hN n hn N (le_refl N)
  by_contra hne
  have h_eq : (dist (u n) (u N) : ℝ) = 1 := by
    change discreteDist (u n) (u N) = 1
    unfold discreteDist
    rw [if_neg hne]
  rw [h_eq] at h_dist
  linarith
/-- **`CompleteSpace` instance.** Every Cauchy sequence in the discrete
metric on `SBoundedProcess` is eventually constant and hence converges
to that constant value.

We use `complete_of_cauchySeq_tendsto`: a uniform space with countable
basis of the uniformity (automatic for metric spaces) is complete iff
every Cauchy *sequence* converges. The discrete metric makes every Cauchy
sequence eventually constant (by `cauchySeq_eventually_constant`), and an
eventually-constant sequence converges to its eventual value. -/
noncomputable instance instCompleteSpaceSBoundedProcess :
    CompleteSpace (SBoundedProcess (n := n) P ℱ T) := by
  apply UniformSpace.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨N, hN⟩ := cauchySeq_eventually_constant u hu
  refine ⟨u N, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨N, fun n hn => ?_⟩
  rw [hN n hn, dist_self]
  exact hε
end DiscreteMetric

end LevyStochCalc.Ito.Picard


