-- Prove2me | Definitions.Def_EngagementOpt_Survey_jointMass
-- name    : EngagementOpt_Survey_jointMass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:27.671051+00:00
-- url     : https://prove2.me/theorems/ec248307-d753-44f8-9cd1-1c16777ce826
-- title:
--   Joint mass $\Pr[T_q=\tau\cap T_p=t-\tau+1]$ of the two phase lengths
-- statement:
--   Let $T_q\sim\mathrm{Geom}(1-q)$ and $T_p\sim\mathrm{Geom}(1-p)$ be independent on $\{1,2,\dots\}$, with laws $g_q$ and $g_p$ (see `geomLaw`). For a session length $t$ and $\tau\in\mathbb N$ define
--
--   $$
--   J_{p,q}(t,\tau)=g_q(\tau)\,g_p(t+1-\tau)=\Pr[T_q=\tau\cap T_p=t-\tau+1].
--   $$
--
--   For $\tau\in\{1,\dots,t\}$ this equals
--
--   $$
--   q^{\tau-1}(1-q)\,p^{t-\tau}(1-p),
--   $$
--
--   the joint mass displayed on p. 20 of the paper. Since the session length is $T=T_q+T_p-1$, these are the masses of the event $\{T=t\}$ split by the value of $T_q$.
--
--   **Formalization Note** The product form encodes the independence of $T_q$ and $T_p$. Natural-number subtraction $t+1-\tau$ is exact on $1\le\tau\le t$, the only range where the definition is used.
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, p. 20, display after (9)

import Mathlib
import Definitions.Def_EngagementOpt_Survey_geomLaw

namespace EngagementOpt.Survey

/-- The joint mass `Pr[T_q = τ ∩ T_p = t - τ + 1]` of the two independent phase lengths
`T_q ∼ Geom(1 - q)` and `T_p ∼ Geom(1 - p)` on `{1, 2, …}` (arXiv:2202.11776v3, pp. 19–20).
For `1 ≤ τ ≤ t` it equals `q ^ (τ - 1) * (1 - q) * p ^ (t - τ) * (1 - p)`; the natural-number
subtraction `t + 1 - τ` is exact on that range. -/
noncomputable def jointMass (p q : ℝ) (t τ : ℕ) : ℝ :=
  geomLaw q τ * geomLaw p (t + 1 - τ)

end EngagementOpt.Survey


