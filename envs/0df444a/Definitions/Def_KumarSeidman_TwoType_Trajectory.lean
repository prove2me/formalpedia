-- Prove2me | Definitions.Def_KumarSeidman_TwoType_Trajectory
-- name    : KumarSeidman_TwoType_Trajectory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:19:22.957597+00:00
-- url     : https://prove2.me/theorems/2f0c4ec0-dab1-4654-9022-b612525cc63b
-- title:
--   §II, p. 290 — fluid trajectories: buffer levels, cumulative flows, runs with set-ups, stability
-- statement:
--   This module defines the continuous-flow (fluid) evolution of a manufacturing system under a schedule of set-ups, together with stability.
--
--   For a buffer $b=b_{p,i}$, let $x_b(t)$ be its level at time $t$, $y_b(t)$ its cumulative output over $[0,t]$, and $u_b(t)$ its cumulative input over $[0,t]$. Parts enter the first buffer of route $p$ from outside, $u_{b_{p,1}}(t)=d_p t$, and every later buffer receives the output of the previous one, $u_{b_{p,i+1}}(t)=y_{b_{p,i}}(t)$. The levels obey
--   $$
--   x_b(t)=x_b(0)+u_b(t)-y_b(t),\qquad x_b(t)\ge 0\quad(t\ge 0),
--   $$
--   with $y_b(0)=0$ and $y_b$ nondecreasing.
--
--   Each machine $m$ works in **runs** $k=0,1,2,\dots$ (finitely or infinitely many). Run $k$ is devoted to a buffer $\beta_k\in B_m$ and starts at time $s_k$, with $s_0=0$. Run $0$ has no set-up. Run $k\ge1$ first spends the set-up time $\delta_{\beta_{k-1},\beta_k}$ and then processes $\beta_k$ until the next run starts. A run is never interrupted during its set-up, and if there are infinitely many runs then $s_k\to\infty$. The trajectory must respect the processing law:
--
--   1. over any interval $[s,t]$, buffer $b$ releases at most $1/\tau_b$ times the time its machine spends processing $b$ in that interval (nothing is processed during set-ups or while the machine serves another buffer);
--   2. if throughout $[s,t)$ the machine is processing $b$ and $b$ is nonempty, then $b$ releases exactly $(t-s)/\tau_b$.
--
--   A machine serving an empty buffer therefore passes on exactly its inflow (the paper's "reduced rate").
--
--   The module also defines the initial state $(x(0),b_0)$ of a trajectory (initial levels and the initial set-up of each machine), the predicate "machine $m$ is set up for $b$ at time $t$", and **stability** (p. 290):
--   $$
--   \sup_{0\le t<\infty}x_{p,i}(t)<+\infty\qquad\text{for every buffer } b_{p,i}.
--   $$
--
--   **Formalization Note** Time is real, and every condition is imposed on $t\ge 0$. "Set up for $b$ at time $t$" means: at $t=0$, the initial set-up; at $t>0$, the buffer of the run $k$ with $s_k<t\le s_{k+1}$. At the start time of a run the machine is thus still set up for the previous buffer, about to commence a set-up away from it. Requiring $s_k\to\infty$ (only finitely many runs start in a bounded interval) is a regularity property of any well-defined schedule, not an extra hypothesis of the paper. Processing time is measured with Lebesgue measure.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 290, §II (levels, stability); p. 289, §I item 4 (set-ups)

import Mathlib
import Definitions.Def_KumarSeidman_TwoType_System

namespace KumarSeidman.TwoType

open MeasureTheory Filter

namespace System

variable (S : System)

/-- The cumulative input `u_{p,i}(t)` of buffer `b_{p,i}` over `[0, t]` (§II, p. 290), given the
cumulative outputs `y` of all buffers: the first buffer of a route receives the external
arrivals `d_p t`; every later buffer receives exactly the cumulative output of the preceding
buffer of the same route (no transport delay). -/
def inflow (y : S.Buffer → ℝ → ℝ) (b : S.Buffer) (t : ℝ) : ℝ :=
  if (b.2 : ℕ) = 0 then S.d b.1 * t
  else y ⟨b.1, ⟨(b.2 : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) b.2.isLt⟩⟩ t

/-- A candidate evolution of the system: buffer levels `x`, cumulative outputs `y`, and for every
machine `m` a schedule of **runs** `k = 0, 1, 2, …` (fewer than `nruns m ∈ ℕ∞` of them).
Run `k` of machine `m` is devoted to buffer `β m k` and starts at time `s m k`. -/
structure Schedule where
  x : S.Buffer → ℝ → ℝ
  y : S.Buffer → ℝ → ℝ
  nruns : Fin S.M → ℕ∞
  β : Fin S.M → ℕ → S.Buffer
  s : Fin S.M → ℕ → ℝ

namespace Schedule

variable {S}
variable (T : S.Schedule)

/-- Run `k` of machine `m` exists. -/
def RunExists (m : Fin S.M) (k : ℕ) : Prop := (k : ℕ∞) < T.nruns m

/-- The start of the processing phase of run `k` of machine `m`: run `0` has no set-up; run
`k + 1` first spends the set-up time `δ_{β_k, β_{k+1}}` and then starts processing. -/
def procStart (m : Fin S.M) : ℕ → ℝ
  | 0 => T.s m 0
  | k + 1 => T.s m (k + 1) + S.δ (T.β m k) (T.β m (k + 1))

/-- At time `t` machine `m` is in the processing phase of its run `k`:
`procStart m k ≤ t < s m (k+1)` (the upper bound only if run `k + 1` exists). -/
def InProcessing (m : Fin S.M) (k : ℕ) (t : ℝ) : Prop :=
  T.RunExists m k ∧ T.procStart m k ≤ t ∧ (T.RunExists m (k + 1) → t < T.s m (k + 1))

/-- At time `t` machine `m` is processing buffer `b` (possibly at a reduced rate if `b` is
empty): it is in the processing phase of a run devoted to `b`. -/
def ProcessingBuffer (m : Fin S.M) (b : S.Buffer) (t : ℝ) : Prop :=
  ∃ k, T.β m k = b ∧ T.InProcessing m k t

/-- The schedule is a fluid trajectory of the system (§I–§II, pp. 289–290, in the form fixed by
the series' canonical model):

1. outputs start at `0` and are nondecreasing on `[0, ∞)`;
2. levels obey `x_b(t) = x_b(0) + u_b(t) − y_b(t)` and are nonnegative for `t ≥ 0`;
3. run `0` of every machine exists and starts at time `0`; every run of machine `m` is devoted
   to a buffer located at `m`; a run is never cut during its set-up phase
   (`procStart m k ≤ s m (k+1)`), so in particular run starts are nondecreasing; if there are
   infinitely many runs, their start times tend to `+∞` (only finitely many runs start in a
   bounded time interval);
4. rate cap: over `[s, t]` buffer `b` releases at most `1/τ_b` times the time its machine spends
   in processing phases of runs devoted to `b` (so nothing is processed during set-ups or while
   the machine is devoted to another buffer);
5. full rate: if throughout `[s, t)` the machine is in a processing phase for `b` and `b` is
   nonempty, then `b` releases exactly `(t − s)/τ_b`. -/
def IsTrajectory : Prop :=
  (∀ b, T.y b 0 = 0) ∧
  (∀ b, MonotoneOn (T.y b) (Set.Ici 0)) ∧
  (∀ b t, 0 ≤ t → T.x b t = T.x b 0 + S.inflow T.y b t - T.y b t) ∧
  (∀ b t, 0 ≤ t → 0 ≤ T.x b t) ∧
  (∀ m, T.RunExists m 0 ∧ T.s m 0 = 0) ∧
  (∀ m k, T.RunExists m k → S.mach (T.β m k) = m) ∧
  (∀ m k, T.RunExists m (k + 1) → T.procStart m k ≤ T.s m (k + 1)) ∧
  (∀ m, T.nruns m = ⊤ → Tendsto (T.s m) atTop atTop) ∧
  (∀ b s t, 0 ≤ s → s ≤ t →
    T.y b t - T.y b s ≤
      (volume {σ | σ ∈ Set.Icc s t ∧ T.ProcessingBuffer (S.mach b) b σ}).toReal / S.procTime b) ∧
  (∀ b s t, 0 ≤ s → s ≤ t →
    (∀ σ ∈ Set.Ico s t, T.ProcessingBuffer (S.mach b) b σ ∧ 0 < T.x b σ) →
    T.y b t - T.y b s = (t - s) / S.procTime b)

/-- The trajectory starts from the initial state `(x₀, b₀)`: initial levels `x₀` and, for every
machine `m`, initial set-up `b₀ m` (the buffer of run `0`). -/
def StartsAt (x₀ : S.Buffer → ℝ) (b₀ : Fin S.M → S.Buffer) : Prop :=
  (∀ b, T.x b 0 = x₀ b) ∧ (∀ m, T.β m 0 = b₀ m)

/-- Machine `m` is set up for buffer `b` at time `t` (convention C8′): at `t = 0` this is the
initial set-up `β m 0`; at `t > 0` it is the buffer of the run `k` with
`s m k < t ≤ s m (k+1)` (the upper bound only if run `k + 1` exists). At the start time of a
run the machine is therefore still set up for the previous buffer. -/
def SetupFor (m : Fin S.M) (t : ℝ) (b : S.Buffer) : Prop :=
  (t = 0 ∧ T.β m 0 = b) ∨
  ∃ k, T.RunExists m k ∧ T.β m k = b ∧ T.s m k < t ∧ (T.RunExists m (k + 1) → t ≤ T.s m (k + 1))

/-- Stability (p. 290): every buffer level is bounded on `[0, ∞)`,
`sup_{0 ≤ t < ∞} x_{p,i}(t) < +∞`. -/
def IsBounded : Prop := ∀ b, BddAbove (T.x b '' Set.Ici 0)

end Schedule

end System

end KumarSeidman.TwoType


