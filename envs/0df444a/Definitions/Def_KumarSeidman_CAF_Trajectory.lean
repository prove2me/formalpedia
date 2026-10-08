-- Prove2me | Definitions.Def_KumarSeidman_CAF_Trajectory
-- name    : KumarSeidman_CAF_Trajectory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:20:47.331238+00:00
-- url     : https://prove2.me/theorems/c952a130-81d4-489a-81cc-568bef0cf0f3
-- title:
--   Fluid trajectories with processing runs and set-ups, and stability (pp. 289–290)
-- statement:
--   The dynamics of a manufacturing system with set-up times under an arbitrary scheduling policy, in the continuous-flow (fluid) form the paper uses throughout (p. 290).
--
--   **Levels.** For each buffer $b$, $x_b(t)\ge 0$ is its level at time $t\ge 0$ and $y_b(t)$ its cumulative output over $[0,t]$, with $y_b(0)=0$ and $y_b$ nondecreasing. The level obeys
--
--   $$
--   x_b(t)=x_b(0)+u_b(t)-y_b(t),
--   $$
--
--   where the cumulative input is $u_{p,1}(t)=d_p\,t$ for the first buffer of a route and $u_{p,i}(t)=y_{p,i-1}(t)$ otherwise (no transport delays). The initial levels $x_b(0)\ge 0$ are arbitrary.
--
--   **Runs.** Each machine $m$ works through a finite or infinite sequence of runs $k=0,1,2,\dots$; run $k$ is on a buffer $\beta_k\in B_m$ and starts at time $s_k$, with $s_0=0$. Run $0$ is on the initial set-up buffer of $m$ and has no set-up. (A machine visited by no route has no buffer to be set up for, and has no runs.) Run $k\ge 1$ consists of a set-up of length $\delta_{\beta_{k-1},\beta_k}$, during which nothing is processed, followed by a processing phase that lasts until $s_{k+1}$ (forever, if it is the last run). A run is never cut during its set-up, $s_{k+1}\ge s_k+\delta_{\beta_{k-1},\beta_k}$, and if there are infinitely many runs then $s_k\to\infty$.
--
--   **Processing.** For $0\le t_1\le t_2$, $y_b(t_2)-y_b(t_1)$ is at most $1/\tau_b$ times the time in $[t_1,t_2]$ during which machine $\mu_b$ is in a processing phase of $b$; and it equals $(t_2-t_1)/\tau_b$ whenever $\mu_b$ processes $b$ throughout $[t_1,t_2]$ and $b$ is nonempty on $[t_1,t_2)$. A machine on an empty buffer thus passes its inflow through.
--
--   **Stability** (p. 290). The trajectory is stable if every buffer level is bounded over all time:
--
--   $$
--   \sup_{0\le t<\infty}x_{p,i}(t)<+\infty\qquad\text{for all } (p,i).
--   $$
--
--   These are the objects of Definitions 1–2 and of Theorem 1.
--
--   **Formalization Note** Time is real with explicit `0 ≤ t`. The number of runs of machine `m` is `N m : ℕ∞` (`⊤` = infinitely many), and `β m k`, `s m k` carry meaning for `k < N m` only. "Time spent processing $b$" is the Lebesgue measure of the set of such times. Run starts are only required to be nondecreasing, so zero-length processing phases are allowed (they occur in the paper's examples). Local finiteness of runs ($s_k\to\infty$) is regularity of a well-defined schedule, not an extra hypothesis. The bound in the stability definition may depend on the trajectory.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 289, §I items 1–4; p. 290, §II (levels, stability, continuous flows)

import Mathlib
import Definitions.Def_KumarSeidman_CAF_System

namespace KumarSeidman.CAF

variable {P M : ℕ}

/-- The cumulative input `u_b(t)` into buffer `b = b_{p,i}` given the cumulative outputs `y`:
external arrivals `d_p t` into the first buffer of a route, and the cumulative output
`y_{p,i-1}(t)` of the preceding buffer otherwise (no transport delay). -/
def inflow (S : System P M) (y : Buffer S → ℝ → ℝ) (b : Buffer S) (t : ℝ) : ℝ :=
  match S.prev b with
  | none => S.d b.1 * t
  | some b' => y b' t

/-- The set-up time paid at the start of run `k` of a machine whose runs are on the buffers
`β 0, β 1, …`: `0` for run `0`, and `δ_{β_{k-1}, β_k}` for run `k ≥ 1`. -/
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

/-- A fluid trajectory of the system `S` under some scheduling policy (§I and §II,
pp. 289–290), from an arbitrary initial state. Time is real, `t ≥ 0`.

* `x b t` is the level of buffer `b` and `y b t` its cumulative output up to time `t`;
  `x_b(t) = x_b(0) + u_b(t) − y_b(t)`, `y_b(0) = 0`, `y_b` nondecreasing, `x_b ≥ 0`.
* Each machine `m` works through runs `k = 0, 1, 2, …` (`N m ∈ ℕ∞` of them, at least one
  if `B_m` is nonempty; `⊤` means infinitely many; a machine visited by no route has no runs). Run `k` is on buffer `β m k ∈ B_m` and starts at `s m k`, with
  `s m 0 = 0`; run `0` is on the initial set-up buffer `β m 0` and has no set-up. Run `k + 1`
  first spends the set-up time `δ_{β m k, β m (k+1)}` (nothing is processed) and then
  processes `β m (k+1)` until the next run starts, or forever if it is the last run. A run is
  never cut during its set-up, and run starts do not accumulate in finite time.
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
  N_pos : ∀ m, (S.B m).Nonempty → 0 < N m
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

/-- The trajectory is **stable** (p. 290): every buffer level is bounded over `[0, ∞)`,
`sup_{0 ≤ t < ∞} x_{p,i}(t) < +∞`. The bound may depend on the trajectory. -/
def IsStable (T : Trajectory S) : Prop := ∀ b, ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → T.x b t ≤ C

end Trajectory

end KumarSeidman.CAF


