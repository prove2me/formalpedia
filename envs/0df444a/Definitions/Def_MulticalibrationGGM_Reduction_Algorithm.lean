-- Prove2me | Definitions.Def_MulticalibrationGGM_Reduction_Algorithm
-- name    : MulticalibrationGGM_Reduction_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:20:53.82018+00:00
-- url     : https://prove2.me/theorems/91f7332d-d808-4a74-9396-763acba95884
-- title:
--   Algorithm 1 and its computed error and regret
-- statement:
--   Fix a class $H$ of tests on $X\times Y$. An external learner consists of an initial state, a next-action function selecting a member of $H$, and a state transition after full loss feedback. A separate EVI oracle has its own state and accepts the current feature $x$, selected test $h$, and tolerance $\varepsilon$; it returns a normalized probability law on the full $Y$ and its next state. Neither machine assumes a multicalibration guarantee.
--
--   The wrapper implements Algorithm 1 in order: Nature reveals $x_t$ from the completed history; the learner chooses $h_t$; the oracle outputs $D_t$; Nature chooses $y_t\in Y$ after seeing $D_t$; and the learner receives the actual loss function
--
--   $$f_t(h)=-\mathbb E_{p\sim D_t}[h(x_t,p)^\top(y_t-p)].$$
--
--   The state recursion determines the trace from these supplied machines, an adaptive Nature, and the tolerance schedule. A prefix is valid when every oracle call satisfies Equation (1) uniformly over $y\in Y$, and each comparator's actual feedback payoff is integrable under that round's law. Correctness is required only at the calls made; this interface does not assert that every bounded discontinuous vector field has an exact zero-tolerance solution.
--
--   From the computed trace, the cumulative quantities are
--
--   $$\mathrm{MC\!\text{-}Err}_T(h)=\sum_{t=1}^T\mathbb E_{p\sim D_t}[h(x_t,p)^\top(y_t-p)],$$
--   $$\mathrm{Regret}_T(h)=\sum_{t=1}^T(f_t(h_t)-f_t(h)),\qquad\mathrm{EVI}_T=\sum_{t=1}^T\varepsilon_t.$$
--
--   Comparator regret uses the referenced general definition of regret with the actual feedback. These definitions provide the source's quantities independently of the target inequality.
--
--   **Formalization Note** Rounds start at 1 and all cumulative sums use that indexing. Round 0 is unused. The learner receives the loss restricted to $H$; on a valid round this is the restriction of a linear functional on the span of $H$, since finite linear combinations of the integrable payoffs remain integrable. State may include a fixed random tape, so the trace interpretation is pathwise and imposes no independence assumption. Nature's outcome may depend on the current law and the full completed history. Empty sums give zero at $T=0$.
-- source:
--   Gabriele Farina, Juan Perdomo, An Efficient Black-Box Reduction from Online Learning to Multicalibration, and a New Route to Φ-Regret Minimization, STOC 2027 submission #721 (October 2026), Algorithm 1 and Equations (1),(2), p. 11; Definition 1, p. 5; Theorem 4, p. 12. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/721.pdf. PDF SHA256: 299cdd3237dbe89568ae8f4a701914eb73339a79fee7d6e00d20cd603b38af44.

import Mathlib
import Definitions.Def_OnlineLearningOCO_FoReL_regret
import Definitions.Def_MulticalibrationGGM_Reduction_Model

open MeasureTheory
open scoped NNReal

namespace MulticalibrationGGM.Reduction

/-!
Farina and Perdomo, STOC 2027 submission #721 (October 2026), Algorithm 1,
Equation (1) and Equation (2), p. 11; Definition 1, p. 5; Theorem 4, p. 12.
https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/721.pdf
PDF SHA256: 299cdd3237dbe89568ae8f4a701914eb73339a79fee7d6e00d20cd603b38af44.
-/

/-- A general full-feedback online learner, unbundled from this paper's test model.
Its next action depends on its state; only after playing does it receive the loss
function restricted to its action set. No performance guarantee is stored here.
For randomized learners the state may include a fixed random tape. -/
structure OnlineLearner (Action State : Type*) where
  initial : State
  choose : State → Action
  update : State → (Action → ℝ) → State

/-- The EVI query interface. The current outcome is absent from the query arguments.
Correctness is required by `ValidRound` at the calls actually made. No universal
existence of an exact (zero-tolerance) EVI solution is assumed. -/
structure EVIOracle (X : Type*) {d : ℕ} (Y : Set (Vector d))
    (H : Set (Test X Y)) (State : Type*) where
  initial : State
  query : State → X → H → ℝ≥0 → ProbabilityMeasure Y × State

/-- One round of Algorithm 1: actual data, with no assumed regret or calibration bound. -/
structure Round (X : Type*) {d : ℕ} (Y : Set (Vector d)) (H : Set (Test X Y)) where
  context : X
  test : H
  forecast : ProbabilityMeasure Y
  outcome : Y
  tolerance : ℝ≥0

/-- Algorithm 1, line 6: the actual loss supplied to the learner, on every action.
It is the restriction of the expected linear test payoff with its sign reversed.
On valid rounds this extends linearly to the span of `H`: integrability is closed
under finite linear combinations. It is not an independently supplied functional. -/
noncomputable def feedback {X : Type*} {d : ℕ} {Y : Set (Vector d)}
    {H : Set (Test X Y)} (r : Round X Y H) (h : H) : ℝ :=
  -expectedPayoff h.val r.context r.forecast r.outcome

/-- Adaptive Nature: the context sees the completed history, and the outcome sees
the current forecast as well. No independence, stochastic model, or measurability
of Nature's choices is required. Histories are chronological. -/
structure Nature (X : Type*) {d : ℕ} (Y : Set (Vector d)) (H : Set (Test X Y)) where
  context : List (Round X Y H) → X
  outcome : List (Round X Y H) → X → ProbabilityMeasure Y → Y

/-- Internal states and the completed history before the next round. -/
structure MachineState (X : Type*) {d : ℕ} (Y : Set (Vector d))
    (H : Set (Test X Y)) (LearnerState OracleState : Type*) where
  learner : LearnerState
  oracle : OracleState
  history : List (Round X Y H)

/-- All six lines of Algorithm 1, in their causal order. Exactly one supplied
learner and one oracle query are used per round. The update receives `feedback r`,
computed only after the current outcome is revealed. -/
noncomputable def algorithmStep {X S Q : Type*} {d : ℕ} {Y : Set (Vector d)}
    {H : Set (Test X Y)} (A : OnlineLearner H S) (O : EVIOracle X Y H Q)
    (N : Nature X Y H) (ε : ℝ≥0) (s : MachineState X Y H S Q) :
    Round X Y H × MachineState X Y H S Q :=
  let x := N.context s.history
  let h := A.choose s.learner
  let answer := O.query s.oracle x h ε
  let y := N.outcome s.history x answer.1
  let r : Round X Y H := ⟨x, h, answer.1, y, ε⟩
  (r, ⟨A.update s.learner (feedback r), answer.2, s.history ++ [r]⟩)

/-- The state after `n` completed rounds, computed by the wrapper from the two
supplied machines and Nature. The source's round numbers start at 1. -/
noncomputable def stateAfter {X S Q : Type*} {d : ℕ} {Y : Set (Vector d)}
    {H : Set (Test X Y)} (A : OnlineLearner H S) (O : EVIOracle X Y H Q)
    (N : Nature X Y H) (ε : ℕ → ℝ≥0) : ℕ → MachineState X Y H S Q
  | 0 => ⟨A.initial, O.initial, []⟩
  | n + 1 => (algorithmStep A O N (ε (n + 1)) (stateAfter A O N ε n)).2

/-- Actual round `t` produced by the causal composition, for `1 ≤ t`.
The value at 0 is unused in every validity condition and cumulative quantity. -/
noncomputable def algorithmRound {X S Q : Type*} {d : ℕ} {Y : Set (Vector d)}
    {H : Set (Test X Y)} (A : OnlineLearner H S) (O : EVIOracle X Y H Q)
    (N : Nature X Y H) (ε : ℕ → ℝ≥0) (t : ℕ) : Round X Y H :=
  (algorithmStep A O N (ε t) (stateAfter A O N ε (t - 1))).1

/-- The primitive's contract and precisely the additional expectation-definedness
needed for feedback: selected-test EVI payoffs for every `y`, and comparator payoffs
at the realized outcome. No calibration bound is part of this condition. -/
def ValidRound {X : Type*} {d : ℕ} {Y : Set (Vector d)}
    {H : Set (Test X Y)} (r : Round X Y H) : Prop :=
  SolvesEVI (r.test.val r.context) r.forecast r.tolerance ∧
  ∀ h ∈ H, Integrable (payoff h r.context r.outcome) (r.forecast : Measure Y)

/-- A prefix has valid oracle calls and well-defined actual feedback. The trace is
computed separately by `algorithmRound`; this predicate supplies neither the trace
nor the claimed calibration/regret inequality. -/
def ValidPrefix {X : Type*} {d : ℕ} {Y : Set (Vector d)}
    {H : Set (Test X Y)} (R : ℕ → Round X Y H) (T : ℕ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, ValidRound (R t)

/-- Definition 1, p. 5: signed cumulative error for the fixed comparator. -/
noncomputable def mcError {X : Type*} {d : ℕ} {Y : Set (Vector d)}
    {H : Set (Test X Y)} (R : ℕ → Round X Y H) (T : ℕ) (h : H) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, expectedPayoff h.val (R t).context (R t).forecast (R t).outcome

/-- Equation (2), p. 11, using the published general comparator-regret definition.
Losses are the computed `feedback`, with the source's sign and round indexing. -/
noncomputable def comparatorRegret {X : Type*} {d : ℕ} {Y : Set (Vector d)}
    {H : Set (Test X Y)} (R : ℕ → Round X Y H) (T : ℕ) (h : H) : ℝ :=
  OnlineLearningOCO.FoReL.regret (fun t => feedback (R t)) (fun t => (R t).test) T h

/-- Theorem 4, p. 12: exact sum of the EVI tolerances, without rescaling. -/
def eviError {X : Type*} {d : ℕ} {Y : Set (Vector d)}
    {H : Set (Test X Y)} (R : ℕ → Round X Y H) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, ((R t).tolerance : ℝ)

end MulticalibrationGGM.Reduction


