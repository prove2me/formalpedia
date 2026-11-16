-- Prove2me | Definitions.Def_MulticalibrationGGM_Reduction_Supplement_Forecaster
-- name    : MulticalibrationGGM_Reduction_Supplement_Forecaster
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:39:33.025764+00:00
-- url     : https://prove2.me/theorems/888c4950-07c6-428d-991a-12b05f6df24c
-- title:
--   Online forecasters, adaptive Nature, best-response Nature and uniform mixtures
-- statement:
--   Fix a feature space $X$, a dimension $d$ and a set $Y\subseteq\mathbb R^d$ of forecasts and outcomes. A **round** of the online protocol of Definition 1 records a context $x_t\in X$, a probability law $D_t$ on the full set $Y$, and an outcome $y_t\in Y$. For any sequence of rounds and any test $h:X\times Y\to\mathbb R^d$, the signed cumulative **multicalibration error** is
--
--   $$\mathrm{MC\text{-}Err}_T(h)=\sum_{t=1}^T\mathbb E_{p_t\sim D_t}\big[h(x_t,p_t)^\top(y_t-p_t)\big].$$
--
--   A **forecaster** has an internal state with an initial value. On context $x$ it outputs a law on $Y$, and after the outcome is revealed it updates its state. **Adaptive Nature** picks the context $x_t$ from the completed history, and the outcome $y_t$ from the history, $x_t$ and the current law $D_t$. Running the two against each other round by round, in this causal order, gives the rounds of the run.
--
--   A forecaster is **$H$-multicalibrated with error bound $B:\mathbb N\to\mathbb R$** if, for every $h\in H$, every adaptive Nature and every horizon $T\ge1$, the run satisfies $\mathrm{MC\text{-}Err}_T(h)\le B(T)$. The bound is required whenever the payoffs of $h$ on that run are integrable under the actual laws.
--
--   For a fixed context $x$ and test $h$, a Nature is a **best-response Nature** at $(x,h)$ if it always plays $x_t=x$ and its outcome is a maximizer
--
--   $$y_t\in\arg\max_{\hat y\in Y}\ \hat y^\top\,\mathbb E_{p\sim D_t}[h(x,p)],$$
--
--   with any tie-breaking and any dependence on the history. Here the expectation is coordinatewise. The **uniform mixture** of laws $D_1,\dots,D_T$ ($T\ge1$) is the probability law $\bar D_T=\frac1T\sum_{t=1}^T D_t$ on $Y$.
--
--   These objects state the converse direction of the paper (Theorem 2, second bullet; §2.1.1): EVIs reduce to online multicalibration.
--
--   **Formalization Note** Coordinates are indexed by `Fin d`. Laws are Mathlib probability measures on the subtype $Y$. Rounds are numbered from 1, and index 0 is unused. A randomized forecaster may keep a fixed random tape in its state.
-- source:
--   Gabriele Farina, Juan Perdomo, An Efficient Black-Box Reduction from Online Learning to Multicalibration, and a New Route to Φ-Regret Minimization, STOC 2027 submission #721 (October 2026), Definition 1, p. 5; §2.1.1, pp. 13–14. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/721.pdf. PDF SHA256: 299cdd3237dbe89568ae8f4a701914eb73339a79fee7d6e00d20cd603b38af44.

import Mathlib
import Definitions.Def_MulticalibrationGGM_Reduction_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MulticalibrationGGM.Reduction.Supplement

/-!
Farina and Perdomo, STOC 2027 submission #721 (October 2026), Definition 1, p. 5;
§2.1.1 (the converse of Theorem 2, second bullet), pp. 13–14.
https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/721.pdf
PDF SHA256: 299cdd3237dbe89568ae8f4a701914eb73339a79fee7d6e00d20cd603b38af44.

A general online forecaster in the protocol of Definition 1, an adaptive Nature, their
causal run, the signed multicalibration error of an arbitrary sequence of rounds, the
hypothesis "H-multicalibrated with error bound B", best-response Nature at a fixed
context, and the uniform mixture of finitely many forecast laws.
-/

/-- One completed round of the protocol of Definition 1: the context `x_t`, the
forecast law `D_t` on the full set `Y`, and the revealed outcome `y_t ∈ Y`. -/
structure FRound (X : Type*) {d : ℕ} (Y : Set (Vector d)) where
  context : X
  forecast : ProbabilityMeasure Y
  outcome : Y

/-- Definition 1, p. 5: signed cumulative multicalibration error
`MC-Err_T(h) = ∑_{t=1}^T E_{p_t ∼ D_t}[h(x_t,p_t)ᵀ(y_t − p_t)]` of an arbitrary sequence of
rounds (rounds are numbered from 1; the value at index 0 is unused). No absolute value. -/
noncomputable def roundsMCError {X : Type*} {d : ℕ} {Y : Set (Vector d)}
    (R : ℕ → FRound X Y) (T : ℕ) (h : Test X Y) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, expectedPayoff h (R t).context (R t).forecast (R t).outcome

/-- A general online forecaster (Definition 1 protocol): an internal state with an initial
value; on context `x` it outputs a probability law on the full `Y`; after the outcome is
revealed it updates its state, seeing the context, its own law and the outcome. No
calibration guarantee is stored here. A randomized forecaster may keep a fixed random tape
in its state. -/
structure Forecaster (X : Type*) {d : ℕ} (Y : Set (Vector d)) (State : Type*) where
  initial : State
  predict : State → X → ProbabilityMeasure Y
  update : State → X → ProbabilityMeasure Y → Y → State

/-- Adaptive Nature: the context may depend on the completed history, and the outcome on
the history, the current context and the current forecast law `D_t`. Histories are
chronological. No stochastic model or measurability is imposed. -/
structure ForecastNature (X : Type*) {d : ℕ} (Y : Set (Vector d)) where
  context : List (FRound X Y) → X
  outcome : List (FRound X Y) → X → ProbabilityMeasure Y → Y

/-- Forecaster state together with the completed history. -/
structure ForecastState (X : Type*) {d : ℕ} (Y : Set (Vector d)) (State : Type*) where
  state : State
  history : List (FRound X Y)

/-- One round, in the causal order of Definition 1: Nature selects `x_t`, the forecaster
outputs `D_t`, Nature reveals `y_t` (after seeing `D_t`), the forecaster updates. -/
noncomputable def forecastStep {X S : Type*} {d : ℕ} {Y : Set (Vector d)}
    (F : Forecaster X Y S) (N : ForecastNature X Y) (s : ForecastState X Y S) :
    FRound X Y × ForecastState X Y S :=
  let x := N.context s.history
  let D := F.predict s.state x
  let y := N.outcome s.history x D
  let r : FRound X Y := ⟨x, D, y⟩
  (r, ⟨F.update s.state x D y, s.history ++ [r]⟩)

/-- State after `n` completed rounds of the run of `F` against `N`. -/
noncomputable def forecastStateAfter {X S : Type*} {d : ℕ} {Y : Set (Vector d)}
    (F : Forecaster X Y S) (N : ForecastNature X Y) : ℕ → ForecastState X Y S
  | 0 => ⟨F.initial, []⟩
  | n + 1 => (forecastStep F N (forecastStateAfter F N n)).2

/-- Round `t` (for `1 ≤ t`) of the run of `F` against `N`. The value at 0 is unused. -/
noncomputable def forecastRound {X S : Type*} {d : ℕ} {Y : Set (Vector d)}
    (F : Forecaster X Y S) (N : ForecastNature X Y) (t : ℕ) : FRound X Y :=
  (forecastStep F N (forecastStateAfter F N (t - 1))).1

/-- §2.1.1, p. 14: `F` is `H`-multicalibrated with error bound `B`: for every test
`h ∈ H`, every adaptive Nature and every horizon `T ≥ 1`, the signed error of the run is at
most `B T`. The bound is required only on runs whose payoffs for `h` are integrable under
the actual laws (the source's convention that its expectations are well defined); this is
a weaker requirement than the inequality on every run. -/
def IsMulticalibratedWithBound {X S : Type*} {d : ℕ} {Y : Set (Vector d)}
    (F : Forecaster X Y S) (H : Set (Test X Y)) (B : ℕ → ℝ) : Prop :=
  ∀ h ∈ H, ∀ N : ForecastNature X Y, ∀ T : ℕ, 1 ≤ T →
    (∀ t ∈ Finset.Icc 1 T,
      Integrable (payoff h (forecastRound F N t).context (forecastRound F N t).outcome)
        ((forecastRound F N t).forecast : Measure Y)) →
    roundsMCError (forecastRound F N) T h ≤ B T

/-- Coordinatewise expectation `E_{p∼D}[g(p)] ∈ ℝ^d`. Every use is guarded by
integrability of the coordinates under the law in question. -/
noncomputable def meanVector {d : ℕ} {Y : Set (Vector d)} (g : Y → Vector d)
    (D : ProbabilityMeasure Y) : Vector d :=
  fun i => ∫ p, g p i ∂(D : Measure Y)

/-- §2.1.1, p. 14: Nature plays `x_t = x` at all times and the outcome is a best response
`y_t ∈ argmax_{ŷ ∈ Y} ŷᵀ E_{p_t∼D_t}[h(x,p_t)]` to the current law, for every history and
every law (any tie-breaking, any dependence on the history). -/
def IsBestResponseNature {X : Type*} {d : ℕ} {Y : Set (Vector d)}
    (h : Test X Y) (x : X) (N : ForecastNature X Y) : Prop :=
  (∀ hist, N.context hist = x) ∧
  ∀ hist (D : ProbabilityMeasure Y) (y' : Y),
    ∑ i : Fin d, y'.val i * meanVector (h x) D i ≤
      ∑ i : Fin d, (N.outcome hist x D).val i * meanVector (h x) D i

/-- The uniform mixture `(1/T) ∑_{t=1}^T D_t` of the laws `D_1, …, D_T`, a probability law
on `Y` for `T ≥ 1`. -/
noncomputable def uniformMixture {d : ℕ} {Y : Set (Vector d)}
    (D : ℕ → ProbabilityMeasure Y) (T : ℕ) (hT : 1 ≤ T) : ProbabilityMeasure Y :=
  ⟨(T : ℝ≥0∞)⁻¹ • ∑ t ∈ Finset.Icc 1 T, (D t : Measure Y), by
    constructor
    have hT0 : (T : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
    simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, measure_univ,
      Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hT0 (ENNReal.natCast_ne_top T)⟩

end MulticalibrationGGM.Reduction.Supplement


