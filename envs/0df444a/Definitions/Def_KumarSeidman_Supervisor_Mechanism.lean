-- Prove2me | Definitions.Def_KumarSeidman_Supervisor_Mechanism
-- name    : KumarSeidman_Supervisor_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:39.232924+00:00
-- url     : https://prove2.me/theorems/6fecfe93-ce36-4757-be79-50fc2c59bcc3
-- title:
--   The universally stabilizing supervisor: truncation, FCFS priority queue $Q_m$, (24), $\zeta_m$ and the backlog $\beta_{p,i}$ (§V)
-- statement:
--   Fix for each machine $m$ a number $\gamma_m$ and for each buffer $b_{p,i}$ a threshold $z_{p,i}\ge 0$. Condition (24) is
--   $$
--   \gamma_m(1-\rho_m)>\sum_{b\in B_m}\max_{b'\in B_m}\delta_{b',b},
--   $$
--   and (26) defines $\zeta_m:=\gamma_m(1-\rho_m)-\sum_{b\in B_m}\max_{b'\in B_m}\delta_{b',b}$, which is positive under (24).
--
--   Each machine $m$ keeps a first-come first-served **priority queue** $Q_m$. A buffer $b_{p,i}\in B_m$ is in $Q_m$ while the machine's current run is not on it and its level exceeds $z_{p,i}$; it enters at the instant both conditions start to hold, and it leaves when a set-up for it commences. A trajectory is **supervised** by $(\gamma,z)$ when, on top of an otherwise arbitrary policy:
--
--   1. **Truncation Rule.** Every run terminates, and no processing run of $b_{p,i}$ lasts longer than $\gamma_m d_p\tau_{p,i}$.
--   2. **Buffer Selection Rule.** If $Q_m\neq\emptyset$ when a run terminates, the next run is on a buffer of $Q_m$ with the earliest entry time. The buffer whose run has just terminated is in $Q_m$ at that instant (at the tail) if its level exceeds its threshold.
--   3. **Processing time for a buffer from $Q_m$.** Such a buffer is processed for exactly $\gamma_m d_p\tau_{p,i}$ time units, unless it clears earlier, in which case the run ends when it clears.
--
--   If $Q_m$ is empty when a run terminates, the next buffer is not restricted.
--
--   For Lemma 1 the file defines when $b$ is in $Q_m$ at an instant $t$, when $b$ **enters** $Q_m$ at $t$, the **subsequent processing run** of $b$ after $t$ (the first run on $b$ that starts at or after $t$ and ends after $t$), and the **backlog**
--   $$
--   \beta_{p,i}(t):=\sum_{j=1}^{i}\tau_{p,i}\,x_{p,j}(t),
--   $$
--   the work machine $\mu_{p,i}$ will spend on the parts now in buffers $b_{p,1},\dots,b_{p,i}$. Every term carries the weight $\tau_{p,i}$, as in the paper.
--
--   The supervisor intervenes only when buffers become large: with large $z$ and $\gamma$ it never acts on a policy that is already stable, while with $z=0$ it enforces FCFS among nonempty buffers.
--
--   **Formalization Note** The queue is not a separate state variable: membership is determined by the trajectory. A buffer that is not processed has a nondecreasing level, so once in $Q_m$ it stays until taken up, and the paper's entering and leaving rules hold. The FCFS key of a waiting buffer is the start of its current sojourn (an infimum); all buffers waiting at time $0$ share the key $0$, and ties are broken arbitrarily, so every initial queue order is allowed.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 296, (24), the five supervisor rules, (26) and Lemma 1 2)

import Mathlib
import Definitions.Def_KumarSeidman_Supervisor_System
import Definitions.Def_KumarSeidman_Supervisor_Trajectory

namespace KumarSeidman.Supervisor

variable {P M : ℕ}

/-- Condition (24) (p. 296) on the supervisor's run-length parameters `γ_m`:
`γ_m (1 − ρ_m) > Σ_{b ∈ B_m} max_{b' ∈ B_m} δ_{b',b}` for every machine `m`. -/
def GammaCondition (S : System P M) (γ : Fin M → ℝ) : Prop :=
  ∀ m, S.setupSum m < γ m * (1 - S.rho m)

/-- `ζ_m := γ_m (1 − ρ_m) − Σ_{b ∈ B_m} max_{b' ∈ B_m} δ_{b',b}`, equation (26) (p. 296). -/
noncomputable def zeta (S : System P M) (γ : Fin M → ℝ) (m : Fin M) : ℝ :=
  γ m * (1 - S.rho m) - S.setupSum m

/-- The truncation length `γ_m d_p τ_{p,i}` of a processing run of buffer `b = b_{p,i}`,
`m = μ_{p,i}`. -/
noncomputable def runCap (S : System P M) (γ : Fin M → ℝ) (b : Buffer S) : ℝ :=
  γ (S.mach b) * S.d b.1 * S.tau b

/-- The backlog `β_{p,i}(t) := Σ_{j=1}^{i} τ_{p,i} x_{p,j}(t)` of Lemma 1 2) (p. 296), for
`b = b_{p,i}`: every term carries the weight `τ_{p,i}` (as printed), the work machine `μ_{p,i}`
will spend on the parts now in the buffers `b_{p,1}, …, b_{p,i}`. -/
noncomputable def backlog {S : System P M} (T : Trajectory S) (b : Buffer S) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.Iic b.2, S.tau b * T.x ⟨b.1, j⟩ t

namespace Trajectory

variable {S : System P M}

/-- Buffer `b` waits in the priority queue `Q_m` (`m = μ_b`) throughout some interval
`(t, t₁)`: on it, machine `m`'s current run is not on `b` and `x_b > z_b` (the two conditions
of the Rule for Entering `Q_m`; a waiting buffer leaves only when a set-up for it commences). -/
def WaitingAfter (T : Trajectory S) (z : Buffer S → ℝ) (b : Buffer S) (t : ℝ) : Prop :=
  ∃ t₁ > t, ∀ σ ∈ Set.Ioo t t₁, ¬ T.OnRun b σ ∧ z b < T.x b σ

/-- The time at which the current sojourn of `b` in `Q_m` began, seen from the instant `t`:
the infimum of the `e ∈ [0, t]` such that `b` was waiting in `Q_m` at every time of `(e, t)`.
This is the FCFS key. All buffers waiting at time `0` share the key `0`, so the initial order
of `Q_m` is arbitrary. -/
noncomputable def entryTime (T : Trajectory S) (z : Buffer S → ℝ) (b : Buffer S) (t : ℝ) : ℝ :=
  sInf {e : ℝ | e ∈ Set.Icc 0 t ∧ ∀ σ ∈ Set.Ioo e t, ¬ T.OnRun b σ ∧ z b < T.x b σ}

/-- The buffers in `Q_m` when run `k` of machine `m` terminates at `s_{k+1}`: every
`b ∈ B_m` with `x_b(s_{k+1}) > z_b`. This includes `β_k` itself if its level exceeds `z_{β_k}`
("after completing a processing run, a buffer may immediately enter `Q_m`", p. 296). -/
def queueAtSwitch (T : Trajectory S) (z : Buffer S → ℝ) (m : Fin M) (k : ℕ) : Set (Buffer S) :=
  {b | S.mach b = m ∧ z b < T.x b (T.s m (k + 1))}

/-- The trajectory obeys the supervisor of §V (p. 296) with parameters `γ` and `z`, on top of
an otherwise arbitrary scheduling policy:

* **Truncation Rule.** Every run terminates, and no processing run of `b_{p,i}` lasts longer
  than `γ_m d_p τ_{p,i}`.
* **Buffer Selection Rule** (with Entering/Leaving `Q_m`). If `Q_m ≠ ∅` when run `k`
  terminates, the next run is on a buffer of `Q_m` with the earliest entry time (FCFS; ties
  are broken arbitrarily).
* **Processing time for a buffer from `Q_m`.** Such a run processes its buffer for exactly
  `γ_m d_p τ_{p,i}` time units, unless the buffer clears earlier, in which case the run ends
  when it clears.

If `Q_m = ∅` when a run terminates, the next buffer is unrestricted. -/
structure Supervised (T : Trajectory S) (γ : Fin M → ℝ) (z : Buffer S → ℝ) : Prop where
  truncation : ∀ m (k : ℕ), (k : ℕ∞) < T.N m →
    T.HasNext m k ∧ T.s m (k + 1) - T.procStart m k ≤ runCap S γ (T.β m k)
  selection : ∀ m (k : ℕ), T.HasNext m k → (T.queueAtSwitch z m k).Nonempty →
    T.β m (k + 1) ∈ T.queueAtSwitch z m k ∧
      ∀ b ∈ T.queueAtSwitch z m k,
        T.entryTime z (T.β m (k + 1)) (T.s m (k + 1)) ≤ T.entryTime z b (T.s m (k + 1))
  queue_time : ∀ m (k : ℕ), T.HasNext m (k + 1) → (T.queueAtSwitch z m k).Nonempty →
    (∀ σ ∈ Set.Ico (T.procStart m (k + 1)) (T.s m (k + 2)), 0 < T.x (T.β m (k + 1)) σ) ∧
      (T.s m (k + 2) = T.procStart m (k + 1) + runCap S γ (T.β m (k + 1)) ∨
        T.x (T.β m (k + 1)) (T.s m (k + 2)) = 0)

/-- Buffer `b` is in `Q_m` at the instant `t`: it waits in `Q_m` just after `t`, or it is in
`Q_m` at a run termination `t = s_{k+1}` and is taken up for processing at that instant. -/
def QueuedAt (T : Trajectory S) (z : Buffer S → ℝ) (b : Buffer S) (t : ℝ) : Prop :=
  0 ≤ t ∧ (T.WaitingAfter z b t ∨
    ∃ k : ℕ, T.HasNext (S.mach b) k ∧ T.s (S.mach b) (k + 1) = t ∧
      T.β (S.mach b) (k + 1) = b ∧ z b < T.x b t)

/-- Buffer `b` enters `Q_m` at the instant `t`: it is in `Q_m` at `t`, and `t = 0` or it was
not waiting in `Q_m` at any time of some interval `(t₀, t)`. -/
def EntersQ (T : Trajectory S) (z : Buffer S → ℝ) (b : Buffer S) (t : ℝ) : Prop :=
  T.QueuedAt z b t ∧ (t = 0 ∨ ∃ t₀ < t, ∀ σ ∈ Set.Ioo t₀ t, ¬ T.WaitingAfter z b σ)

/-- Run `k` of machine `μ_b` is the first processing run of `b` subsequent to the instant `t`:
it is on `b`, starts at or after `t` and ends after `t`, and no earlier run on `b` does both.
Its completion time is `s_{k+1}`. -/
def IsNextRun (T : Trajectory S) (b : Buffer S) (t : ℝ) (k : ℕ) : Prop :=
  (k : ℕ∞) < T.N (S.mach b) ∧ T.β (S.mach b) k = b ∧ t ≤ T.s (S.mach b) k ∧
    (T.HasNext (S.mach b) k → t < T.s (S.mach b) (k + 1)) ∧
    ∀ j < k, T.β (S.mach b) j = b →
      ¬ (t ≤ T.s (S.mach b) j ∧ (T.HasNext (S.mach b) j → t < T.s (S.mach b) (j + 1)))

end Trajectory

end KumarSeidman.Supervisor


