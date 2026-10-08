-- Prove2me | Definitions.Def_KumarSeidman_TwoType_Clearing
-- name    : KumarSeidman_TwoType_Clearing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:34.395616+00:00
-- url     : https://prove2.me/theorems/2aebe7dc-7223-47fd-9707-60f6f09eccba
-- title:
--   Definition 1, p. 290 — clearing policies
-- statement:
--   This module formalizes Definition 1 of the paper: a scheduling policy is **clearing** if, whenever a machine $m$ is processing parts in a buffer $b\in B_m$, it remains set up for $b$ and keeps processing it until the first time thereafter that simultaneously $b$ is empty and some other buffer $b'\in B_m$ is nonempty; at that time it commences a set-up for one of the nonempty buffers of $B_m$.
--
--   Here a buffer $b'$ counts as nonempty at time $t$ (is **demanding**) if
--   $$
--   x_{b'}(t)>0\quad\text{or}\quad u_{b'}(\sigma)>u_{b'}(t)\ \text{ for all }\sigma>t,
--   $$
--   that is, it holds parts or starts receiving parts at $t$. A buffer fed by external arrivals is always demanding.
--
--   Run by run, a trajectory is clearing when, for every machine $m$ and every run $k$ devoted to $b=\beta_k$:
--
--   1. at no time strictly inside the processing phase of run $k$ is $b$ empty while another buffer of $B_m$ is demanding;
--   2. if run $k+1$ exists, then at its start $s_{k+1}$ buffer $b$ is empty, and $\beta_{k+1}\neq b$ is a demanding buffer of $B_m$.
--
--   Together these two conditions force the switch at the first instant at which $b$ is empty and another buffer of $m$ is demanding. A **clearing trajectory from** $(x_0,b_0)$ is a trajectory of the system that starts at that state and is clearing.
--
--   **Formalization Note** The literal reading "$x_{b'}(t)>0$" would make the paper's own trajectories (Example 1; Example 2, Case 2, machine 2 at $t_2$) non-clearing, since the target buffer has level exactly $0$ at the switching instant and fills immediately afterwards; "the first time" would not exist. The demanding reading is the one under which the paper's examples are clearing trajectories. Condition 1 is on the open processing interval, so that with zero or short set-ups a machine may start processing a buffer that is still empty but being fed.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 290, Definition 1

import Mathlib
import Definitions.Def_KumarSeidman_TwoType_Trajectory

namespace KumarSeidman.TwoType

namespace System

namespace Schedule

variable {S : System} (T : S.Schedule)

/-- Buffer `b` is *demanding* at time `t` (the reading of "nonempty" in Definition 1 used by the
series): it is nonempty, or its cumulative input strictly increases after `t` (it is being fed
from time `t` on). A buffer receiving external arrivals is always demanding. -/
def Demanding (b : S.Buffer) (t : ℝ) : Prop :=
  0 < T.x b t ∨ ∀ σ, t < σ → S.inflow T.y b t < S.inflow T.y b σ

/-- The clearing rule of Definition 1 (p. 290), run by run. For every machine `m` and every run
`k` of `m`, devoted to buffer `b = β m k`:

* (no early exit) at no time `t` strictly inside the processing phase of run `k` is `b` empty
  while some other buffer `b' ≠ b` of machine `m` is demanding;
* (exit) if run `k + 1` exists, then at its start time `s m (k+1)` buffer `b` is empty, and run
  `k + 1` is devoted to a buffer of `m` other than `b` that is demanding at that time.

Together these say that the machine keeps processing `b` until the first time that
simultaneously `b` is empty and some other buffer of `m` is demanding, and then commences a
set-up for one of the demanding buffers. -/
def IsClearing : Prop :=
  ∀ m k, T.RunExists m k →
    (∀ t, T.procStart m k < t → (T.RunExists m (k + 1) → t < T.s m (k + 1)) →
      ¬ (T.x (T.β m k) t = 0 ∧
          ∃ b', S.mach b' = m ∧ b' ≠ T.β m k ∧ T.Demanding b' t)) ∧
    (T.RunExists m (k + 1) →
      T.x (T.β m k) (T.s m (k + 1)) = 0 ∧ T.β m (k + 1) ≠ T.β m k ∧
        T.Demanding (T.β m (k + 1)) (T.s m (k + 1)))

/-- A clearing trajectory from the initial state `(x₀, b₀)`: a fluid trajectory of the system
that starts at `(x₀, b₀)` and follows the clearing rule. -/
def IsClearingFrom (x₀ : S.Buffer → ℝ) (b₀ : Fin S.M → S.Buffer) : Prop :=
  T.IsTrajectory ∧ T.StartsAt x₀ b₀ ∧ T.IsClearing

end Schedule

end System

end KumarSeidman.TwoType


