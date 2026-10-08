-- Prove2me | Definitions.Def_KumarSeidman_Supervisor_Trajectory
-- name    : KumarSeidman_Supervisor_Trajectory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:20:32.743991+00:00
-- url     : https://prove2.me/theorems/88089b50-fa90-45c1-a8b4-3958bac83ef5
-- title:
--   Fluid trajectories of a manufacturing system under an arbitrary scheduling policy (§I–§II)
-- statement:
--   This file fixes the continuous-flow dynamics of the system under an **arbitrary** scheduling policy, starting from an arbitrary initial state. Time is real and $t\ge 0$.
--
--   1. **Levels and outputs.** Buffer $b$ has the level $x_b(t)\ge 0$ and the cumulative output $y_b(t)$, with $y_b(0)=0$ and $y_b$ nondecreasing. The balance equation is
--   $$
--   x_b(t)=x_b(0)+u_b(t)-y_b(t),
--   $$
--   where the cumulative input is $u_{p,1}(t)=d_p t$ for the first buffer of a route and $u_{p,i}(t)=y_{p,i-1}(t)$ otherwise. There is no transport delay. The initial levels $x_b(0)\ge 0$ are arbitrary.
--   2. **Runs.** Each machine $m$ works through a sequence of runs $k=0,1,2,\dots$ (finitely or infinitely many). Run $k$ is on a buffer $\beta_{m,k}\in B_m$ and starts at time $s_{m,k}$, with $s_{m,0}=0$. Run $0$ is on the initial set-up buffer and has no set-up. Run $k\ge 1$ first spends the set-up time $\delta_{\beta_{m,k-1},\beta_{m,k}}$, during which nothing is processed, and then processes $\beta_{m,k}$ until run $k+1$ starts (or forever if it is the last run). A run is never interrupted during its set-up, and run starts do not accumulate in finite time. A machine is always in some run, so it never idles outside the run structure.
--   3. **Processing law.** On every interval $[t_1,t_2]$, $y_b$ grows by at most $1/\tau_b$ times the length of the time that machine $\mu_b$ spends in processing phases of $b$. On an interval throughout which $\mu_b$ processes $b$ and $b$ is nonempty, $y_b$ grows at exactly the rate $1/\tau_b$. A machine processing an empty buffer therefore passes the inflow through at a reduced rate.
--
--   The trajectory is **stable** if every buffer level is bounded on $[0,\infty)$:
--   $$
--   \sup_{0\le t<\infty} x_{p,i}(t)<+\infty\qquad\text{for all }p,i .
--   $$
--   The bound may depend on the trajectory.
--
--   The file also names the predicate "the current run of machine $\mu_b$ at time $\sigma$ is on $b$" (in its set-up or its processing phase), which the supervisor's queue rules refer to.
--
--   **Formalization Note** The number of runs of machine $m$ is `N m : ℕ∞`. The occupancy of processing phases is measured with Lebesgue measure. Run starts are non-decreasing (zero-length runs are allowed); local finiteness ($s_{m,k}\to\infty$ when there are infinitely many runs) is regularity of a well-defined schedule. At a run start $s_{m,k+1}$ the current run is run $k+1$.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 289, §I; p. 290, §II (buffer dynamics, definition of stability)

import Mathlib
import Definitions.Def_KumarSeidman_Supervisor_System

namespace KumarSeidman.Supervisor

variable {P M : ℕ}

/-- The cumulative input `u_b(t)` into buffer `b = b_{p,i}` given the cumulative outputs `y`:
external arrivals `d_p t` into the first buffer of a route, and the cumulative output
`y_{p,i-1}(t)` of the preceding buffer otherwise (no transport delay). -/
def inflow (S : System P M) (y : Buffer S → ℝ → ℝ) (b : Buffer S) (t : ℝ) : ℝ :=
  match S.prev b with
  | none => S.d b.1 * t
  | some b' => y b' t

/-- The set-up time paid at the start of run `k` of a machine whose runs are on the buffers
`β 0, β 1, …`: `0` for run `0`, and `δ_{β_{k-1}, β_k}` for run `k ≥ 1` (which is `0` when
`β_{k-1} = β_k`, since `δ_{b,b} = 0`). -/
def runSetup (S : System P M) (β : ℕ → Buffer S) : ℕ → ℝ
  | 0 => 0
  | j + 1 => S.δ (β j) (β (j + 1))

/-- For a machine with `N ∈ ℕ∞` runs on the buffers `β k` starting at the times `s k`:
run `k` exists and the machine is in its processing phase at time `σ`, i.e.
`s_k + δ_{β_{k-1},β_k} ≤ σ`, and `σ < s_{k+1}` if run `k + 1` exists. -/
def InProcPhase (S : System P M) (N : ℕ∞) (β : ℕ → Buffer S) (s : ℕ → ℝ) (k : ℕ) (σ : ℝ) :
    Prop :=
  (k : ℕ∞) < N ∧ s k + runSetup S β k ≤ σ ∧ (((k + 1 : ℕ) : ℕ∞) < N → σ < s (k + 1))

/-- The machine with run data `(N, β, s)` is in a processing phase of buffer `b` at time `σ`. -/
def ProcessesAt (S : System P M) (N : ℕ∞) (β : ℕ → Buffer S) (s : ℕ → ℝ) (b : Buffer S)
    (σ : ℝ) : Prop :=
  ∃ k : ℕ, β k = b ∧ InProcPhase S N β s k σ

/-- A fluid trajectory of the system `S` under an arbitrary scheduling policy (§I and §II,
pp. 289–290), from an arbitrary initial state. Time is real, `t ≥ 0`.

* `x b t` is the level of buffer `b` and `y b t` its cumulative output up to time `t`;
  `x_b(t) = x_b(0) + u_b(t) − y_b(t)`, `y_b(0) = 0`, `y_b` nondecreasing, `x_b ≥ 0`.
* Each machine `m` works through runs `k = 0, 1, 2, …` (`N m ∈ ℕ∞` of them, at least one;
  `⊤` means infinitely many). Run `k` is on buffer `β m k ∈ B_m` and starts at `s m k`, with
  `s m 0 = 0`; run `0` is on the initial set-up buffer `β m 0` and has no set-up. Run `k + 1`
  first spends the set-up time `δ_{β m k, β m (k+1)}` (nothing is processed) and then
  processes `β m (k+1)` until the next run starts, or forever if it is the last run. A run is
  never cut during its set-up, and run starts do not accumulate in finite time. The machine
  is always in some run: it never idles outside the run structure.
* Processing law: `y_b` grows at most at rate `1/τ_b`, and only while machine `μ_b` is in a
  processing phase of `b`; it grows at exactly rate `1/τ_b` on an interval throughout which
  `μ_b` processes `b` and `b` is nonempty. -/
structure Trajectory (S : System P M) where
  x : Buffer S → ℝ → ℝ
  y : Buffer S → ℝ → ℝ
  N : Fin M → ℕ∞
  β : Fin M → ℕ → Buffer S
  s : Fin M → ℕ → ℝ
  y_zero : ∀ b, y b 0 = 0
  y_mono : ∀ b, MonotoneOn (y b) (Set.Ici 0)
  balance : ∀ b t, 0 ≤ t → x b t = x b 0 + inflow S y b t - y b t
  x_nonneg : ∀ b t, 0 ≤ t → 0 ≤ x b t
  N_pos : ∀ m, 0 < N m
  β_mem : ∀ m (k : ℕ), (k : ℕ∞) < N m → S.mach (β m k) = m
  s_zero : ∀ m, s m 0 = 0
  setup_not_cut : ∀ m (k : ℕ), ((k + 1 : ℕ) : ℕ∞) < N m →
    s m k + runSetup S (β m) k ≤ s m (k + 1)
  locally_finite : ∀ m, N m = ⊤ → Filter.Tendsto (s m) Filter.atTop Filter.atTop
  rate_cap : ∀ b (t₁ t₂ : ℝ), 0 ≤ t₁ → t₁ ≤ t₂ →
    y b t₂ - y b t₁ ≤
      (MeasureTheory.volume (Set.Icc t₁ t₂ ∩
        {σ | ProcessesAt S (N (S.mach b)) (β (S.mach b)) (s (S.mach b)) b σ})).toReal / S.tau b
  full_rate : ∀ b (t₁ t₂ : ℝ), 0 ≤ t₁ → t₁ ≤ t₂ →
    (∀ σ ∈ Set.Icc t₁ t₂, ProcessesAt S (N (S.mach b)) (β (S.mach b)) (s (S.mach b)) b σ) →
    (∀ σ ∈ Set.Ico t₁ t₂, 0 < x b σ) →
    y b t₂ - y b t₁ = (t₂ - t₁) / S.tau b

namespace Trajectory

variable {S : System P M}

/-- Run `k + 1` of machine `m` exists (so run `k` ends at the set-up commencement
`s m (k + 1)`). -/
def HasNext (T : Trajectory S) (m : Fin M) (k : ℕ) : Prop := ((k + 1 : ℕ) : ℕ∞) < T.N m

/-- The time at which the processing phase of run `k` of machine `m` begins:
`s_k + δ_{β_{k-1}, β_k}` (`= s_0 = 0` for run `0`). -/
def procStart (T : Trajectory S) (m : Fin M) (k : ℕ) : ℝ := T.s m k + runSetup S (T.β m) k

/-- The current run of machine `μ_b` at time `σ` is on buffer `b` (in its set-up phase or in
its processing phase): some run `k` on `b` has `s_k ≤ σ` and, if run `k + 1` exists,
`σ < s_{k+1}`. At a run start `s_{k+1}` the current run is run `k + 1`. -/
def OnRun (T : Trajectory S) (b : Buffer S) (σ : ℝ) : Prop :=
  ∃ k : ℕ, (k : ℕ∞) < T.N (S.mach b) ∧ T.β (S.mach b) k = b ∧ T.s (S.mach b) k ≤ σ ∧
    (T.HasNext (S.mach b) k → σ < T.s (S.mach b) (k + 1))

/-- The trajectory is **stable** (p. 290): every buffer level is bounded over `[0, ∞)`,
`sup_{0 ≤ t < ∞} x_{p,i}(t) < +∞`. The bound may depend on the trajectory. -/
def IsStable (T : Trajectory S) : Prop := ∀ b, ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → T.x b t ≤ C

end Trajectory

end KumarSeidman.Supervisor


