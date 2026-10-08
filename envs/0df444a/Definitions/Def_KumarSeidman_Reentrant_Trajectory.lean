-- Prove2me | Definitions.Def_KumarSeidman_Reentrant_Trajectory
-- name    : KumarSeidman_Reentrant_Trajectory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:56:22.632724+00:00
-- url     : https://prove2.me/theorems/1d9e1bba-dec2-402e-8203-358336779865
-- title:
--   §II, p. 290 — fluid trajectories: buffer levels, cumulative outputs, runs with set-up and processing phases
-- statement:
--   A **fluid trajectory** of a manufacturing system records, for real time $t \ge 0$, the level $x_b(t)$ of every buffer $b$, its cumulative output $y_b(t)$ over $[0,t]$, and the schedule of every machine.
--
--   The schedule of machine $m$ is a finite or infinite sequence of **runs** $k = 0, 1, 2, \dots$. Run $k$ works on a buffer $\beta_k \in B_m$ and starts at time $s_k$, with $s_0 = 0$; run $0$ is on the machine's initial set-up buffer and has no set-up. Run $k \ge 1$ consists of a **set-up phase** $[s_k, s_k + \delta_{\beta_{k-1},\beta_k})$ followed by a **processing phase** $[a_k, s_{k+1})$, where $a_k = s_k + \delta_{\beta_{k-1},\beta_k}$ (and $a_0 = 0$); the last run of a finite schedule lasts forever. A trajectory satisfies:
--
--   1. $y_b(0) = 0$ and $y_b$ is nondecreasing on $[0,\infty)$;
--   2. $x_b(t) = x_b(0) + u_b(t) - y_b(t) \ge 0$ for $t \ge 0$ (§II);
--   3. every run of machine $m$ is on a buffer of $B_m$, and a run is never cut during its set-up: $a_k \le s_{k+1}$;
--   4. only finitely many runs of each machine start in any bounded time interval;
--   5. (rate cap) for $0 \le s \le t$,
--   $$y_b(t) - y_b(s) \le \frac{1}{\tau_b}\,\bigl|\{\sigma \in [s,t] : \text{machine } \mu_b \text{ is in a processing phase of } b \text{ at } \sigma\}\bigr|,$$
--   where $|\cdot|$ is Lebesgue measure; in particular nothing is processed during a set-up;
--   6. (full rate when nonempty) if throughout $[s,t)$ machine $\mu_b$ is in a processing phase of $b$ and $x_b > 0$, then $y_b(t) - y_b(s) = (t-s)/\tau_b$.
--
--   A machine is always in a set-up or a processing phase; a machine processing an empty buffer passes its inflow through at the inflow rate, as in the paper's Example 1 ("the rate at which machine 1 works on buffer 1 drops to 1 to match the input rate exactly").
--
--   Machine $m$ is **set up for** buffer $b$ at time $t$ if $t = 0$ and $b$ is its initial buffer, or if $b = \beta_k$ for the run $k$ with $s_k < t \le s_{k+1}$ (or $s_k < t$ when run $k$ is the last). At a run's start time the machine is still set up for the previous buffer and is commencing a set-up away from it.
--
--   **Formalization Note** Time is `ℝ` with explicit `0 ≤ t` hypotheses; values at negative times are unconstrained and never used. The number of runs is `N m : ℕ∞`, and run `k` exists iff `k < N m`. The paper states the fluid dynamics in prose and refers to Perkins–Kumar for the model; items 3–6 are that model written out (contiguous runs, no idling outside runs, local finiteness of run starts). Run starts are only required to be nondecreasing, so zero-length processing phases are allowed, as at time $0$ in Example 1.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 290, §II (x_{p,i}(t) = x_{p,i}(0) + u_{p,i}(t) − y_{p,i}(t), continuous flows); p. 289, §I item 4) (set-up times)

import Mathlib
import Definitions.Def_KumarSeidman_Reentrant_System

namespace KumarSeidman.Reentrant

open MeasureTheory

/-- The data of a fluid trajectory of a manufacturing system (§II, p. 290), with real time
`t ≥ 0`:

* `x b t` is the level of buffer `b` at time `t` and `y b t` its cumulative output over `[0, t]`;
* the schedule of machine `m` is a sequence of **runs** `k = 0, 1, 2, …`; `N m ∈ ℕ ∪ {∞}` is the
  number of runs (the last run of a finite schedule lasts forever), run `k` is on buffer
  `β m k` and starts at time `s m k`. Run `0` is on the machine's initial set-up buffer
  `β m 0` and has no set-up; run `k ≥ 1` begins with a set-up phase of length
  `δ (β m (k-1)) (β m k)` followed by a processing phase that lasts until `s m (k+1)`. -/
structure Trajectory {P M : ℕ} {n : Fin P → ℕ} (S : System P M n) where
  x : Buffer P n → ℝ → ℝ
  y : Buffer P n → ℝ → ℝ
  N : Fin M → ℕ∞
  β : Fin M → ℕ → Buffer P n
  s : Fin M → ℕ → ℝ

variable {P M : ℕ} {n : Fin P → ℕ} {S : System P M n}

/-- Run `k` of machine `m` exists. -/
def Trajectory.RunExists (T : Trajectory S) (m : Fin M) (k : ℕ) : Prop :=
  (k : ℕ∞) < T.N m

/-- The set-up time paid at the start of run `k` of machine `m`: none for run `0`, and
`δ_{β_k, β_{k+1}}` for run `k + 1`. -/
def Trajectory.setupTime (T : Trajectory S) (m : Fin M) : ℕ → ℝ
  | 0 => 0
  | k + 1 => S.δ (T.β m k) (T.β m (k + 1))

/-- The time `a_k = s_k + (set-up time of run k)` at which the processing phase of run `k` of
machine `m` begins. -/
def Trajectory.procStart (T : Trajectory S) (m : Fin M) (k : ℕ) : ℝ :=
  T.s m k + T.setupTime m k

/-- Machine `m` is in a processing phase of buffer `b` at time `σ`: for some run `k` on `b`,
`a_k ≤ σ` and, if run `k + 1` exists, `σ < s_{k+1}`. -/
def Trajectory.Processing (T : Trajectory S) (m : Fin M) (b : Buffer P n) (σ : ℝ) : Prop :=
  ∃ k, T.RunExists m k ∧ T.β m k = b ∧ T.procStart m k ≤ σ ∧
    (T.RunExists m (k + 1) → σ < T.s m (k + 1))

/-- `T` is a fluid trajectory of `S` (§II, p. 290, with the run structure of §I, item 4)):

1. `y_b(0) = 0`, `y_b` is nondecreasing on `[0, ∞)`;
2. `x_b(t) = x_b(0) + u_b(t) - y_b(t)` and `x_b(t) ≥ 0` for `t ≥ 0`, where `u_b` is
   `S.input y b`;
3. every machine has a run `0`, starting at time `0`; every run of machine `m` is on a buffer
   served by `m`; a run is never cut during its set-up (`a_k ≤ s_{k+1}`);
4. only finitely many runs of a machine start in any bounded time interval;
5. rate cap and exclusivity: for `0 ≤ s ≤ t`, `y_b(t) - y_b(s)` is at most `1/τ_b` times the
   Lebesgue measure of the set of times in `[s, t]` at which the machine `μ_b` is in a
   processing phase of `b` (so nothing is processed during set-ups or while another buffer is
   processed);
6. full rate when nonempty: if throughout `[s, t)` the machine `μ_b` is in a processing phase of
   `b` and `x_b > 0`, then `y_b(t) - y_b(s) = (t - s)/τ_b`. -/
def IsTrajectory (S : System P M n) (T : Trajectory S) : Prop :=
  (∀ b, T.y b 0 = 0) ∧
  (∀ b, MonotoneOn (T.y b) (Set.Ici 0)) ∧
  (∀ b t, 0 ≤ t → T.x b t = T.x b 0 + S.input T.y b t - T.y b t) ∧
  (∀ b t, 0 ≤ t → 0 ≤ T.x b t) ∧
  (∀ m, T.RunExists m 0) ∧
  (∀ m, T.s m 0 = 0) ∧
  (∀ m k, T.RunExists m k → S.route (T.β m k) = m) ∧
  (∀ m k, T.RunExists m (k + 1) → T.procStart m k ≤ T.s m (k + 1)) ∧
  (∀ m (t : ℝ), {k : ℕ | T.RunExists m k ∧ T.s m k ≤ t}.Finite) ∧
  (∀ b (s t : ℝ), 0 ≤ s → s ≤ t →
    T.y b t - T.y b s ≤
      (volume (Set.Icc s t ∩ {σ | T.Processing (S.route b) b σ})).toReal / S.τ b) ∧
  (∀ b (s t : ℝ), 0 ≤ s → s ≤ t →
    (∀ σ ∈ Set.Ico s t, T.Processing (S.route b) b σ ∧ 0 < T.x b σ) →
    T.y b t - T.y b s = (t - s) / S.τ b)

/-- Machine `m` is set up for buffer `b` at time `t` (§III): at `t = 0` it is set up for its
initial buffer `β m 0`; at `t > 0` it is set up for the buffer of the run `k` with
`s_k < t ≤ s_{k+1}` (or `s_k < t` if run `k` is the last). At the start time of a run the
machine is still set up for the previous buffer and is commencing a set-up away from it. -/
def Trajectory.IsSetUpFor (T : Trajectory S) (m : Fin M) (t : ℝ) (b : Buffer P n) : Prop :=
  (t = 0 ∧ T.β m 0 = b) ∨
  ∃ k, T.RunExists m k ∧ T.β m k = b ∧ T.s m k < t ∧
    (T.RunExists m (k + 1) → t ≤ T.s m (k + 1))

end KumarSeidman.Reentrant


