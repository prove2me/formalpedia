-- Prove2me | Definitions.Def_VolunteerNotify_IsDP
-- name    : VolunteerNotify_IsDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:37:32.429047+00:00
-- url     : https://prove2.me/theorems/a8937d16-69fc-4736-9c4e-f06b91d55709
-- title:
--   (6)–(8) — the dynamic programs $(\tilde x,J)$ of the sparse notification policy
-- statement:
--   Fix an input $x$. For $v=1,\dots,V$ in order and $t=T,\dots,1$, with $J_{v,T+1}=0$, the source defines
--   $$
--   r_{v,s,t}=p_{v,s}\prod_{u=1}^{v-1}(1-\tilde x_{u,s,t}p_{u,s}), \tag{6}
--   $$
--   $$
--   \tilde x_{v,s,t}=x_{v,s,t}\,\mathbb I\Bigl(r_{v,s,t}+\sum_{\tau=t+1}^T g(\tau-t)J_{v,\tau}\ge J_{v,t+1}\Bigr), \tag{7}
--   $$
--   $$
--   J_{v,t}=\sum_{s=0}^S\lambda_{s,t}\Bigl((1-\tilde x_{v,s,t})J_{v,t+1}+\tilde x_{v,s,t}\bigl(r_{v,s,t}+\sum_{\tau=t+1}^T g(\tau-t)J_{v,\tau}\bigr)\Bigr). \tag{8}
--   $$
--   Variables of type $0$ are $0$, so the $s=0$ term is $\lambda_{0,t}J_{v,t+1}$. `IsDP I x xt J` states that $(\tilde x,J)$ satisfies these equations. They determine $(\tilde x,J)$ uniquely for every input.
--
--   The vector $\tilde x$ is the sparsified solution that Algorithm 1 follows online, and $J_{v,t}$ is a lower bound on what $v$ completes from $t$ on when active at $t$.
--
--   **Formalization Note** A row of $J$ has type `Fin (T + 1) → ℝ`: `J v 0` is $J_{v,1}$, `t.castSucc` is period $t$, `t.succ` is $t+1$, and `Fin.last T` is $T+1$.
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, (6)–(8), fn. 18, p.16; Algorithm 1, p.17

import Mathlib
import Definitions.Def_VolunteerNotify_Instance

namespace VolunteerNotify

variable {V S T : ℕ}

/-- The reward `r_{v,s,t} := p_{v,s} ∏_{u=1}^{v−1} (1 − x̃_{u,s,t} p_{u,s})`, Manshadi–Rodilitz,
arXiv:2002.08474v7, (6), p.16. -/
noncomputable def reward (I : Instance V S T) (xt : Decision V S T) (v : Fin V) (s : Fin S)
    (t : Fin T) : ℝ :=
  I.p v s * ∏ u ∈ Finset.Iio v, (1 - xt u s t * I.p u s)

/-- The future value `∑_{τ=t+1}^T g(τ − t) J_τ` of a notification at `t`, arXiv:2002.08474v7,
(7), (8), p.16. It is an empty sum at the last period.

**Formalization Note.** A value function `J : Fin (T + 1) → ℝ` holds `J_1, …, J_{T+1}`: `J 0` is
`J_1`, `t.castSucc` is paper period `t`, `t.succ` is `t + 1` and `Fin.last T` is `T + 1`. -/
noncomputable def futureValue (I : Instance V S T) (J : Fin (T + 1) → ℝ) (t : Fin T) : ℝ :=
  ∑ τ ∈ Finset.Ioi t, I.g ((τ : ℕ) - (t : ℕ)) * J τ.castSucc

/-- `(x̃, J)` is the solution of the dynamic programs of the sparse notification policy for the
input `x`, arXiv:2002.08474v7, (6)–(8), p.16 and Algorithm 1, p.17: `J_{v,T+1} = 0`,

  `x̃_{v,s,t} = x_{v,s,t} 𝕀(r_{v,s,t} + ∑_{τ=t+1}^T g(τ − t) J_{v,τ} ≥ J_{v,t+1})`,

  `J_{v,t} = ∑_{s=0}^S λ_{s,t} ((1 − x̃_{v,s,t}) J_{v,t+1} + x̃_{v,s,t} (r_{v,s,t} + ∑_{τ=t+1}^T g(τ − t) J_{v,τ}))`.

**Formalization Note.** The `s = 0` term of (8) has `x̃_{v,0,t} = 0` (fn. 18), so it is
`λ_{0,t} J_{v,t+1}`. The equations determine `(x̃, J)` uniquely, processing `v` in order and `t`
backwards, because row `v` uses `x̃` only at `u < v` and `J_v` only at later periods. -/
structure IsDP (I : Instance V S T) (x xt : Decision V S T) (J : Fin V → Fin (T + 1) → ℝ) :
    Prop where
  terminal : ∀ v, J v (Fin.last T) = 0
  sparsify : ∀ v s t, xt v s t = x v s t *
    (if J v t.succ ≤ reward I xt v s t + futureValue I (J v) t then 1 else 0)
  value : ∀ v t, J v t.castSucc = I.noTask t * J v t.succ +
    ∑ s, I.lam s t * ((1 - xt v s t) * J v t.succ +
      xt v s t * (reward I xt v s t + futureValue I (J v) t))

end VolunteerNotify


