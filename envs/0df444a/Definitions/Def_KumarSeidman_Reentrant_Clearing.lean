-- Prove2me | Definitions.Def_KumarSeidman_Reentrant_Clearing
-- name    : KumarSeidman_Reentrant_Clearing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:13:55.793629+00:00
-- url     : https://prove2.me/theorems/bd93d31a-6f4c-46a7-ad22-097f3fd4642f
-- title:
--   Definition 1, p. 290 — clearing policies
-- statement:
--   Definition 1 of the paper: a scheduling policy is a **clearing policy** if, whenever a machine $m$ is processing parts in a buffer $b \in B_m$, it continues to remain set up for and to process parts from $b$ until the first time thereafter that simultaneously $b$ is empty and some other buffer $b' \in B_m$ is nonempty; at such a time the machine commences a set-up for one of the nonempty buffers of $B_m$.
--
--   Here a buffer $b'$ counts as nonempty at time $t$ when it is **demanding**:
--   $$x_{b'}(t) > 0 \quad\text{or}\quad u_{b'}(t) < u_{b'}(\sigma) \ \text{ for every } \sigma > t,$$
--   that is, it holds material or its inflow starts at $t$.
--
--   A trajectory is a **clearing trajectory** if, for every machine $m$ and every run $k$ of $m$ on buffer $b = \beta_k$ with processing phase $[a_k, s_{k+1})$:
--
--   1. (no early exit) at no time $t$ with $a_k < t < s_{k+1}$ is $b$ empty while some buffer $b' \in B_m$, $b' \ne b$, is demanding;
--   2. (exit) if run $k+1$ exists, then $x_b(s_{k+1}) = 0$, $\beta_{k+1} \ne b$, and $\beta_{k+1}$ is demanding at $s_{k+1}$.
--
--   Together these force the switch at the first instant at which $b$ is empty and another buffer of the machine is demanding.
--
--   **Formalization Note** "Nonempty" for the target buffer is read as *demanding*. In the paper's own trajectories the buffer a machine switches to often has level exactly $0$ at the switching instant and starts to fill immediately afterwards (Example 1, Case 1, at $t_2$ and $t_6$; Case 2, at $t_3$); with the literal test $x_{b'}(t) > 0$ the set of switching times would be open at its left end, "the first time" would not exist, and those trajectories would not be clearing. The emptiness test on the current buffer is literal, $x_b(t) = 0$. Condition 1 is imposed on the open interval $(a_k, s_{k+1})$: with zero set-up times a machine starts processing a buffer at the instant it selects it, possibly while another buffer is already demanding, and a closed interval would forbid every trajectory of Example 1, Case 2.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 290, Definition 1

import Mathlib
import Definitions.Def_KumarSeidman_Reentrant_System
import Definitions.Def_KumarSeidman_Reentrant_Trajectory

namespace KumarSeidman.Reentrant

variable {P M : ℕ} {n : Fin P → ℕ} {S : System P M n}

/-- Buffer `b` is *demanding* at time `t`: it is nonempty, `x_b(t) > 0`, or its inflow starts
at `t`, i.e. `u_b(t) < u_b(σ)` for every `σ > t`. This is the reading of "nonempty" in
Definition 1 (p. 290) under which the paper's own trajectories are clearing trajectories: in
them the buffer a machine switches to often has level exactly `0` at the switching instant and
starts to fill immediately afterwards. A buffer fed by external arrivals is always demanding. -/
def Trajectory.Demanding (T : Trajectory S) (b : Buffer P n) (t : ℝ) : Prop :=
  0 < T.x b t ∨ ∀ σ : ℝ, t < σ → S.input T.y b t < S.input T.y b σ

/-- `T` is a trajectory of `S` under a **clearing policy** (Definition 1, p. 290): a machine
processing a buffer `b` keeps processing `b` until the first time thereafter that
simultaneously `b` is empty and some other buffer of the machine is (in the sense of
`Demanding`) nonempty; at that time it commences a set-up for one of those buffers. For every
machine `m` and every run `k` on `b = β_k` with processing phase `[a_k, s_{k+1})`:

1. (no early exit) for every `t` with `a_k < t` and, if run `k + 1` exists, `t < s_{k+1}`, it is
   not the case that `x_b(t) = 0` and some buffer `b' ≠ b` served by `m` is demanding at `t`;
2. (exit) if run `k + 1` exists, then at `s_{k+1}` the buffer `b` is empty, `β_{k+1} ≠ b`, and
   `β_{k+1}` is demanding at `s_{k+1}`. -/
def IsClearing (S : System P M n) (T : Trajectory S) : Prop :=
  IsTrajectory S T ∧
  ∀ m k, T.RunExists m k →
    (∀ t : ℝ, T.procStart m k < t → (T.RunExists m (k + 1) → t < T.s m (k + 1)) →
      ¬ (T.x (T.β m k) t = 0 ∧
          ∃ b', S.route b' = m ∧ b' ≠ T.β m k ∧ T.Demanding b' t)) ∧
    (T.RunExists m (k + 1) →
      T.x (T.β m k) (T.s m (k + 1)) = 0 ∧ T.β m (k + 1) ≠ T.β m k ∧
        T.Demanding (T.β m (k + 1)) (T.s m (k + 1)))

end KumarSeidman.Reentrant


