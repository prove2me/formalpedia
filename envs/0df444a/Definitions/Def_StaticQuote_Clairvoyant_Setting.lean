-- Prove2me | Definitions.Def_StaticQuote_Clairvoyant_Setting
-- name    : StaticQuote_Clairvoyant_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:31.132979+00:00
-- url     : https://prove2.me/theorems/30c0f69f-5366-4ca5-be08-8c7564d7ae74
-- title:
--   §3, (4), (12), pp. 8–11, 18 — the GI/G/1 sample-path model, g, FCFS schedules, the long-run cost (4) and the clairvoyant value γ_{i:j}
-- statement:
--   This file fixes the model of a single-server queue of orders with a common promised pickup time, and the two quantities compared by the clairvoyant lower bound.
--
--   **The model (§3, p. 8).** On a probability space $(\Omega,\mathcal F,\mu)$ live inter-arrival times $T_1,T_2,\dots$ and service times $x_1,x_2,\dots$. The family $\{T_n\}_{n\ge1}\cup\{x_n\}_{n\ge1}$ is mutually independent, the $T_n$ are identically distributed with mean $1/\lambda$, the $x_n$ are identically distributed with mean $1/\mu$, and $\lambda<\mu$ (stability). Customer $n\ge1$ arrives at
--   $$t_n = T_1+T_2+\cdots+T_n$$
--   and is due (promised pickup) at $d_n = t_n+\delta$, where $\delta\ge0$ is the common quote time. The arrival rate is $\lambda = 1/\mathbb E[T_1]$. The standing assumptions `Standing` collect all of this, together with the sign conditions that durations are nonnegative almost surely and that $\delta, c_e, c_d \ge 0$.
--
--   **Cost (p. 9).** A customer whose service ends at $D_n$ pays $g(D_n-d_n)$, where
--   $$g(\xi) = c_e(-\xi)^+ + c_d(\xi)^+$$
--   charges earliness at rate $c_e$ and tardiness at rate $c_d$.
--
--   **Schedules.** A schedule assigns to each customer $n$ and sample path $\omega$ a service start time $y_n(\omega)$. It is *FCFS-feasible* if on every sample path and for all $n\ge1$
--   $$y_n \ge t_n, \qquad y_{n+1} \ge y_n + x_n,$$
--   and customer $n$ then departs at $D_n = y_n + x_n$.
--
--   **Long-run average cost, form (4) (p. 11).** The long-run expected average cost of a schedule $y$ is
--   $$C(y) = \lambda\,\limsup_{N\to\infty} \mathbb E\Big[\frac{1}{N}\sum_{n=1}^N g(y_n+x_n-d_n)\Big].$$
--
--   **Perfectly-clairvoyant value (12) (p. 18).** For customers $i$ through $j$ and a sample path $\omega$,
--   $$\gamma_{i:j}(\omega) = \inf_{y}\ \sum_{n=i}^{j} g(y_n + x_n - d_n) \quad\text{s.t.}\quad y_n\ge t_n\ (n=i,\dots,j),\quad y_{n+1}\ge y_n+x_n\ (n=i,\dots,j-1),$$
--   the least cost of these customers when every inter-arrival and service time is known in advance.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Customers are indexed from $1$; the coordinates $T_0, x_0$ are unused and carry no hypothesis. The outcome $\omega$ is the whole sample path of inter-arrival and service times. The paper's policy classes (admissible, FCFS, Loynes stable) are not modelled: every policy of the paper's class $\Pi$ yields an FCFS-feasible schedule, and statements quantify over all of these. $C$ is defined by the per-customer form (4) rather than by the calendar-time form (1). The value $\gamma_{i:j}$, the costs, the expectations (lower Lebesgue integrals) and the $\limsup$ all take values in $[0,\infty]$, so an infimum, an expectation or a $\limsup$ can never collapse to a junk value; each cost term is $\max(g,0)$, which equals $g$ when $c_e,c_d\ge0$. "Mean $1/\lambda$" and "mean $1/\mu$" are read as $0<\mathbb E[T_1]<\infty$ and $0<\mathbb E[x_1]<\infty$; $\lambda<\mu$ is $\mathbb E[x_1]<\mathbb E[T_1]$.
-- source:
--   Farahani, Dawande, Janakiraman, Order Now, Pickup in 30 Minutes, SSRN 3557605 (version of 2021-08-05), pp. 8–11, 18, §3, (4), (12)

import Mathlib

/-!
# The GI/G/1 sample-path model with a static quote time, and its perfectly-clairvoyant value

Farahani, Dawande, Janakiraman, Order Now, Pickup in 30 Minutes, SSRN 3557605 (version of 2021-08-05),
pp. 8–11 and 18, §3 (primitives, g, (4)) and §6.1 (program (12)).

**Formalization Notes.**
* Customers are indexed from `1`, as on the page: `t_n = T_1 + ⋯ + T_n`. The coordinates `T 0`, `x 0`
  are never used and carry no hypothesis.
* The outcome `ω : Ω` is the full sample path of inter-arrival **and** service times (the page's ω⃗;
  p. 18 calls it "a sample path of inter-arrival times", p. 19 "of inter-arrival and service times").
* Policies are not modelled. The policy class is the class of start-time schedules `y : ℕ → Ω → ℝ`
  that are FCFS-feasible on every sample path (`IsFCFSSchedule`); every policy of the paper's classes
  `Π ⊆ Π_FCFS` gives such a schedule (p. 18, proof of Theorem 4).
* The long-run average cost `C^π` is defined by its per-customer form (4) (p. 11), not by (1).
* `γ_{i:j}` is an infimum in `ℝ≥0∞` (the page writes `min`); costs, expectations (`lintegral`) and
  `lim sup`s are all in `ℝ≥0∞`, so no junk value of a real `⨅`, `limsup` or Bochner integral enters.
  Each summand is `ENNReal.ofReal (g …)`, exact because `g ≥ 0` when `c_e, c_d ≥ 0`.
* `Standing` adds the sign conditions the page leaves implicit (durations nonnegative, `δ, c_e, c_d ≥ 0`)
  and reads "mean `1/λ`", "mean `1/µ`" as `0 < E[T_1] < ∞`, `0 < E[x_1] < ∞`; stability `λ < µ` is
  `E[x_1] < E[T_1]`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace StaticQuote.Clairvoyant

/-- The earliness–tardiness cost `g(ξ) = c_e (−ξ)^+ + c_d (ξ)^+` (p. 9). -/
def g (ce cd ξ : ℝ) : ℝ := ce * max (-ξ) 0 + cd * max ξ 0

/-- The data of the model (§3, p. 8) on an outcome space `Ω`: inter-arrival times `T n`, service times
`x n` (customers `n ≥ 1`), the common quote time `δ`, and the unit earliness and tardiness costs. -/
structure Model (Ω : Type*) where
  /-- inter-arrival time of customer `n` (`n ≥ 1`) -/
  T : ℕ → Ω → ℝ
  /-- service time of customer `n` (`n ≥ 1`) -/
  x : ℕ → Ω → ℝ
  /-- the common quote time -/
  δ : ℝ
  /-- earliness cost per unit time -/
  ce : ℝ
  /-- tardiness cost per unit time -/
  cd : ℝ

namespace Model

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The standing assumptions of §3 (p. 8): a probability space carrying i.i.d. inter-arrival times
`T_1, T_2, …` (mean `1/λ`) and i.i.d. service times `x_1, x_2, …` (mean `1/µ`), the whole family
mutually independent, with `λ < µ`; plus the implicit sign conditions. -/
def Standing (Q : Model Ω) (μ : Measure Ω) : Prop :=
  IsProbabilityMeasure μ ∧
  (∀ n, 1 ≤ n → Measurable (Q.T n)) ∧ (∀ n, 1 ≤ n → Measurable (Q.x n)) ∧
  -- mutual independence of `{T_n}_{n ≥ 1} ∪ {x_n}_{n ≥ 1}`
  iIndepFun (fun i : ℕ ⊕ ℕ => Sum.elim (fun n => Q.T (n + 1)) (fun n => Q.x (n + 1)) i) μ ∧
  -- identical distribution
  (∀ n, 1 ≤ n → IdentDistrib (Q.T n) (Q.T 1) μ μ) ∧
  (∀ n, 1 ≤ n → IdentDistrib (Q.x n) (Q.x 1) μ μ) ∧
  -- durations are nonnegative
  (∀ n, 1 ≤ n → 0 ≤ᵐ[μ] Q.T n) ∧ (∀ n, 1 ≤ n → 0 ≤ᵐ[μ] Q.x n) ∧
  -- means `1/λ` and `1/µ`, and stability `λ < µ`
  Integrable (Q.T 1) μ ∧ 0 < ∫ ω, Q.T 1 ω ∂μ ∧
  Integrable (Q.x 1) μ ∧ 0 < ∫ ω, Q.x 1 ω ∂μ ∧
  ∫ ω, Q.x 1 ω ∂μ < ∫ ω, Q.T 1 ω ∂μ ∧
  -- sign conditions on the quote time and the unit costs
  0 ≤ Q.δ ∧ 0 ≤ Q.ce ∧ 0 ≤ Q.cd

/-- The arrival rate `λ = 1 / E[T_1]`. -/
noncomputable def rate (Q : Model Ω) (μ : Measure Ω) : ℝ := 1 / ∫ ω, Q.T 1 ω ∂μ

/-- Arrival time `t_n = T_1 + ⋯ + T_n` of customer `n` (p. 8). -/
def arrival (Q : Model Ω) (n : ℕ) (ω : Ω) : ℝ := ∑ k ∈ Finset.Icc 1 n, Q.T k ω

/-- Due date `d_n = t_n + δ` of customer `n` (p. 8). -/
def due (Q : Model Ω) (n : ℕ) (ω : Ω) : ℝ := Q.arrival n ω + Q.δ

/-- A start-time schedule `y` (`y n ω` = start of service of customer `n` on the path `ω`) is
FCFS-feasible on every sample path: `y_n ≥ t_n` and `y_{n+1} ≥ y_n + x_n` for all `n ≥ 1`
(p. 18, proof of Theorem 4). Departure times are `D_n = y_n + x_n`. -/
def IsFCFSSchedule (Q : Model Ω) (y : ℕ → Ω → ℝ) : Prop :=
  ∀ ω, ∀ n, 1 ≤ n → Q.arrival n ω ≤ y n ω ∧ y n ω + Q.x n ω ≤ y (n + 1) ω

/-- The long-run average cost of a schedule, in the per-customer form (4) (p. 11):
`C^π = λ lim sup_{N→∞} E[Σ_{n=1}^N g(y_n + x_n − d_n) / N]`
(`W^π_n + x_n − δ = y_n + x_n − d_n` with `W^π_n = y_n − t_n`). -/
noncomputable def cost (Q : Model Ω) (μ : Measure Ω) (y : ℕ → Ω → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Q.rate μ) *
    limsup (fun N : ℕ => ∫⁻ ω, (∑ n ∈ Finset.Icc 1 N,
      ENNReal.ofReal (g Q.ce Q.cd (y n ω + Q.x n ω - Q.due n ω))) / (N : ℝ≥0∞) ∂μ) atTop

/-- The constraints of the clairvoyant program (12) on the path `ω` for customers `i, …, j`:
`y_n ≥ t_n` for `n = i, …, j` and `y_{n+1} ≥ y_n + x_n` for `n = i, …, j − 1`. -/
def IsSchedule (Q : Model Ω) (i j : ℕ) (y : ℕ → ℝ) (ω : Ω) : Prop :=
  (∀ n ∈ Finset.Icc i j, Q.arrival n ω ≤ y n) ∧
  (∀ n ∈ Finset.Ico i j, y n + Q.x n ω ≤ y (n + 1))

/-- The perfectly-clairvoyant value (12) (p. 18): the least cost of customers `i` through `j` on the
path `ω`, `γ_{i:j}(ω) = inf { Σ_{n=i}^j g(y_n + x_n − d_n) : y feasible for (12) }`, in `ℝ≥0∞`. -/
noncomputable def gamma (Q : Model Ω) (i j : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (y : ℕ → ℝ) (_ : Q.IsSchedule i j y ω),
    ∑ n ∈ Finset.Icc i j, ENNReal.ofReal (g Q.ce Q.cd (y n + Q.x n ω - Q.due n ω))

end Model

end StaticQuote.Clairvoyant


