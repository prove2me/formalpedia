-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardSpaceDiscrete
-- name    : KLSModular_LevyStochCalc_Ito_PicardSpaceDiscrete
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:43:46.436809+00:00
-- url     : https://prove2.me/theorems/544bc8a7-0669-4c7d-b867-e9fcc32835f9
-- title:
--   Discrete metric and completeness for bounded processes
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc). `constantZeroProcess` gives a zero element of `SBoundedProcess`, and `discreteDist X Y` is $0$ when $X=Y$ and $1$ otherwise. The supplied pseudo-metric and metric instances use this distance, and the bundle proves that every Cauchy sequence is eventually constant and that the resulting metric space is complete. This discrete metric is separate from the analytic Bielecki norm.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Ito.Picard
--   import Mathlib.Topology.MetricSpace.Basic
--   import Mathlib.Topology.MetricSpace.Contracting
--   import Mathlib.Topology.UniformSpace.Cauchy
--   import Mathlib.Topology.UniformSpace.UniformEmbedding
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   noncomputable def constantZeroProcess
--       {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
--       (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (T : ℝ) :
--       SBoundedProcess (n := n) P ℱ T
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Ito/Picard`](https://prove2.me/theorems/641877d8-7533-4330-9f7d-6b397b95165e).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardSpaceDiscrete.lean) · `LevyStochCalc.Ito.PicardSpaceDiscrete` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardSpaceDiscrete.lean#L34-L259 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardSpaceDiscrete`, definition bundle `KLSModular_LevyStochCalc_Ito_PicardSpaceDiscrete`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_Picard
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardSpaceDiscrete.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Ito
namespace Picard
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
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
section DiscreteMetric
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
end Picard
end Ito
end LevyStochCalc


