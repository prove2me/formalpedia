-- Prove2me | Definitions.Def_MTSActionPredictions_SyncRestart_Supplement_Predictions
-- name    : MTSActionPredictions_SyncRestart_Supplement_Predictions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:27:31.131502+00:00
-- url     : https://prove2.me/theorems/d999bf7b-983a-4ba3-abcd-27175382cd63
-- title:
--   Algorithms with action predictions on a general MTS, ball restriction, and upper expectation
-- statement:
--   Let $(M,d)$ be a metric space with start state $x_0$, and let a model specify the valid service cost functions $c:M\to[0,\infty]$ (the published base model). An **input with action predictions** is a finite sequence of pairs $(c_1,P_1),\dots,(c_T,P_T)$: at time $t$ the service cost function $c_t$ and a predicted state $P_t\in M$ are revealed together, and $P_0=x_0$.
--
--   1. A **randomized online algorithm with action predictions** is a map that, given a private random seed $\omega$, the start state and the revealed prefix $(c_1,P_1),\dots,(c_t,P_t)$, returns the state $x_t$; $x_0$ is the start state. It never sees future requests, the horizon or any offline solution. A deterministic algorithm is the case of a one-point seed space.
--   2. Its **cost** is $\sum_{t=1}^T\big(d(x_{t-1},x_t)+c_t(x_t)\big)\in[0,\infty]$, and the **prediction error** of the input against an offline trajectory $O$ with $O_0=x_0$ is $\eta(P,O)=\sum_{t=1}^T d(P_t,O_t)$; both are the published base quantities.
--   3. **Scalar measurability** of an algorithm from $x_0$: on every valid input, its total cost and the distance from its final state to any fixed state are measurable functions of the seed.
--   4. The **upper expectation** of $f:\Omega\to[0,\infty]$ is $\overline{\mathbb E}[f]=\inf\{\mathbb E[g]: g\ \text{measurable},\ g\ge f\}$; it equals $\mathbb E[f]$ when $f$ is measurable.
--   5. For $r\ge0$ the **ball restriction** of a task is
--   $$c^{\le r}(x)=\begin{cases}c(x),& d(x,x_0)\le r,\\ \infty,&\text{otherwise},\end{cases}$$
--   and a model is **restriction closed** when $c^{\le r}$ is valid for every valid $c$ and every $r\ge0$.
--
--   These objects state the combination results of Section 8 (Lemma 37, Theorem 5) for general metrical task systems, reusing the base cost and error.
--
--   **Formalization Note** Inputs are lists of (task, prediction) pairs, entry $i$ being time $i+1$. Costs are in $[0,\infty]$ (`ENNReal`). The upper expectation is used for the existentially constructed combination algorithms, so that their bounds never rely on a non-measurable cost being underestimated by the lower Lebesgue integral.
-- source:
--   Júlia Baligács, Christian Coester, Alexa Tudose, STOC 2027 submission #1248 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1248.pdf; §1.1, PDF pp. 2–3 / printed pp. 1–2; Theorem 5, PDF pp. 4–5 and 28 / printed pp. 3–4 and 27; Lemma 37, PDF pp. 25–26 / printed pp. 24–25

import Definitions.Def_MTSActionPredictions_SyncRestart_Model

open scoped ENNReal BigOperators
open MeasureTheory

namespace MTSActionPredictions.SyncRestart.Supplement

open MTSActionPredictions.SyncRestart

/-! # Algorithms with action predictions on a general MTS (§1.1, PDF 2–3 / printed 1–2; §8, PDF 25–30)

An input with action predictions is a finite list of pairs `(c_t, P_t)`: the service task revealed
at time `t` and the predicted state revealed with it. List entry `i` is time `i + 1`; `P_0 = x_0`.
The costs and errors are the published base primitives `trajectoryCost` and `predictionError`. -/

/-- A causal randomized algorithm with action predictions: a private seed, the common start
state, and the revealed prefix of (task, prediction) pairs determine the current state. It has no
access to future requests, the horizon, or any comparator. A deterministic algorithm is the case
`Ω = Unit`. -/
abbrev PRule (Ω M : Type*) := Ω → M → List (Task M × M) → M

/-- The service tasks of an input with predictions. -/
def tasks {M : Type*} (q : List (Task M × M)) : List (Task M) := q.map Prod.fst

/-- The prediction sequence: `P_0 = x_0` and `P_{t}` is the prediction revealed at time `t`. -/
def predSeq {M : Type*} (x : M) (q : List (Task M × M)) : ℕ → M
  | 0 => x
  | t + 1 => (q.getD t ((fun _ => 0), x)).2

/-- The state at time `t` (time `0` is the start state). -/
def ptraj {Ω M : Type*} (A : PRule Ω M) (ω : Ω) (x : M) (q : List (Task M × M)) (t : ℕ) : M :=
  if t = 0 then x else A ω x (q.take t)

/-- Movement plus service cost of the algorithm on the whole input, in `[0, ∞]`. -/
noncomputable def pcost {Ω M : Type*} [MetricSpace M] (A : PRule Ω M) (ω : Ω) (x : M)
    (q : List (Task M × M)) : ℝ≥0∞ :=
  trajectoryCost (tasks q) (ptraj A ω x q)

/-- The action-prediction error `η(P, OFF) = ∑_{t=1}^T d(P_t, O_t)` of the input's predictions
against an offline trajectory `O`. -/
noncomputable def perror {M : Type*} [MetricSpace M] (x : M) (q : List (Task M × M))
    (O : ℕ → M) : ℝ≥0∞ :=
  predictionError q.length (predSeq x q) O

/-- Scalar measurability of a randomized algorithm from start `x₀` on valid inputs: its total cost
and the distances from its final state to fixed states are measurable functions of the seed. -/
def PScalarMeasurable {Ω M : Type*} [MeasurableSpace Ω] [MetricSpace M] (model : Model M)
    (x₀ : M) (A : PRule Ω M) : Prop :=
  (∀ q, ValidTasks model (tasks q) → Measurable (fun ω => pcost A ω x₀ q)) ∧
  (∀ q y, ValidTasks model (tasks q) → Measurable (fun ω => edist (ptraj A ω x₀ q q.length) y))

/-- The upper (outer) expectation of a `[0, ∞]`-valued function: the infimum of the expectations of
its measurable majorants. It equals `∫⁻ f ∂μ` whenever `f` is measurable, and otherwise bounds every
measurable minorant's expectation from above, so a bound on it is never easier than a bound on a
genuine expectation. -/
noncomputable def upperExp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ≥0∞) :
    ℝ≥0∞ :=
  ⨅ (g : Ω → ℝ≥0∞) (_ : Measurable g) (_ : f ≤ g), ∫⁻ ω, g ω ∂μ

/-- The ball restriction `c^{≤r}` of a task around the start state `x₀` (Theorem 5, PDF 4 / 28):
equal to `c` on the closed ball of radius `r` around `x₀` and `∞` outside it. -/
noncomputable def ballRestrict {M : Type*} [MetricSpace M] (x₀ : M) (r : ℝ) (c : Task M) :
    Task M :=
  fun x => if dist x x₀ ≤ r then c x else ⊤

/-- The structural property of Theorem 5: every ball restriction of a valid service cost function
around the start state is again a valid service cost function. -/
def RestrictionClosed {M : Type*} [MetricSpace M] (model : Model M) (x₀ : M) : Prop :=
  ∀ c ∈ model.allowed, ∀ r : ℝ, 0 ≤ r → ballRestrict x₀ r c ∈ model.allowed

end MTSActionPredictions.SyncRestart.Supplement


