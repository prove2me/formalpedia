-- Prove2me | Definitions.Def_KumarSeidman_CAF_Policy
-- name    : KumarSeidman_CAF_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:47.367294+00:00
-- url     : https://prove2.me/theorems/5fd7ed43-56dd-40b3-83bb-4c98892a79a4
-- title:
--   Clearing policies (Definition 1) and clear-a-fraction policies (Definition 2)
-- statement:
--   The two policy classes of §II (p. 290), as properties of a trajectory.
--
--   **Demanding buffers.** A buffer $b$ is *demanding* at time $t$ if it is nonempty, $x_b(t)>0$, or its inflow starts at $t$, i.e. $u_b(t)<u_b(\sigma)$ for every $\sigma>t$.
--
--   **Definition 1 (clearing policy).** Whenever machine $m$ is processing parts in a buffer $b\in B_m$, it continues to remain set up for and to process parts from $b$ until the first time thereafter that simultaneously $b$ is empty and some other buffer $b'\in B_m$ is demanding; at such a time it commences a set-up for one of the demanding buffers. In terms of runs: for every run $k$ of machine $m$, on buffer $b=\beta_k$, with processing phase starting at $a_k=s_k+\delta_{\beta_{k-1},\beta_k}$,
--
--   1. at no time $t$ with $a_k<t<s_{k+1}$ is $b$ empty while another buffer of $B_m$ is demanding;
--   2. if run $k+1$ exists, then $x_b(s_{k+1})=0$, and the next buffer $\beta_{k+1}\ne b$ is demanding at $s_{k+1}$.
--
--   **Definition 2 (clear-a-fraction policy).** A clearing trajectory is CAF with constants $\varepsilon_m>0$ and $K_m\in\mathbb R$ if, whenever machine $m$ commences a set-up to buffer $b_{p,i}\in B_m$ at time $t$ (the start of a run $k\ge1$),
--
--   $$
--   x_{p,i}(t)\ \ge\ \varepsilon_m\sum_{(q,j):\,\mu_{q,j}=m}x_{q,j}(t)-K_m. \tag{2}
--   $$
--
--   Theorem 1 asserts that, under condition (14), every CAF trajectory is stable.
--
--   **Formalization Note** Definition 1 says "nonempty" for the buffer to switch to. In the paper's own trajectories the selected buffer has level exactly $0$ at the switching instant and starts filling immediately afterwards; read literally ($x_{b'}>0$), the set of switching times would be open at its left end and "the first time" would not exist. "Nonempty" is therefore read as *demanding*; a buffer fed by external arrivals is always demanding. The emptiness test on the current buffer is literal. The no-early-exit condition is imposed on the open interval $(a_k,s_{k+1})$, so that a machine may start processing a buffer it has just selected while that buffer is still empty and only being fed. The constants $\varepsilon,K$ are parameters of the predicate; "a CAF policy" means some $\varepsilon>0$, $K$.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 290, Definition 1 and Definition 2, (2)

import Mathlib
import Definitions.Def_KumarSeidman_CAF_Trajectory

namespace KumarSeidman.CAF

variable {P M : ℕ} {S : System P M}

namespace Trajectory

/-- Buffer `b` is **demanding** at time `t`: it is nonempty, or its inflow starts at `t`
(`u_b(t) < u_b(σ)` for every `σ > t`). This is the reading of "nonempty" in Definition 1
(p. 290) under which the paper's own example trajectories are clearing trajectories. -/
def Demanding (T : Trajectory S) (b : Buffer S) (t : ℝ) : Prop :=
  0 < T.x b t ∨ ∀ σ : ℝ, t < σ → inflow S T.y b t < inflow S T.y b σ

/-- **Clearing policy** (Definition 1, p. 290). For every machine `m` and every run `k` of
`m`, on buffer `b = β m k`, with processing phase starting at `a_k = s_k + δ_{β_{k-1},β_k}`:
1. (no early exit) at no time `t` with `a_k < t < s_{k+1}` (or `a_k < t` if run `k` is the
   last) is `b` empty while some other buffer `b' ∈ B_m` is demanding;
2. (exit) if run `k + 1` exists, then at its start `s_{k+1}` the buffer `b` is empty, and
   the newly selected buffer `β m (k+1) ≠ b` is demanding.
Together these force the switch at the first time after `a_k` at which `b` is empty and some
other buffer of `B_m` is demanding. -/
def IsClearing (T : Trajectory S) : Prop :=
  ∀ (m : Fin M) (k : ℕ), (k : ℕ∞) < T.N m →
    (∀ t : ℝ, T.procStart m k < t → (T.HasNext m k → t < T.s m (k + 1)) →
      ¬ (T.x (T.β m k) t = 0 ∧ ∃ b' ∈ S.B m, b' ≠ T.β m k ∧ T.Demanding b' t)) ∧
    (T.HasNext m k →
      T.x (T.β m k) (T.s m (k + 1)) = 0 ∧ T.β m (k + 1) ≠ T.β m k ∧
        T.Demanding (T.β m (k + 1)) (T.s m (k + 1)))

/-- **Clear-a-fraction (CAF) policy** (Definition 2, p. 290) with constants `ε_m > 0` and
`K_m ∈ ℝ`: a clearing trajectory such that whenever machine `m` commences a set-up to buffer
`b_{p,i}` (the start `s_k` of a run `k ≥ 1`), (2) holds:
`x_{p,i}(s_k) ≥ ε_m Σ_{(q,j): μ_{q,j} = m} x_{q,j}(s_k) − K_m`. -/
def IsCAF (T : Trajectory S) (ε K : Fin M → ℝ) : Prop :=
  T.IsClearing ∧ (∀ m, 0 < ε m) ∧
    ∀ (m : Fin M) (k : ℕ), 1 ≤ k → (k : ℕ∞) < T.N m →
      ε m * ∑ b ∈ S.B m, T.x b (T.s m k) - K m ≤ T.x (T.β m k) (T.s m k)

end Trajectory

end KumarSeidman.CAF


