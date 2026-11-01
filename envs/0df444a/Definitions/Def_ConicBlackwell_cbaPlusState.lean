-- Prove2me | Definitions.Def_ConicBlackwell_cbaPlusState
-- name    : ConicBlackwell_cbaPlusState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:44:06.390977+00:00
-- url     : https://prove2.me/theorems/d9ea0b45-d68a-463c-8521-06fb1068d150
-- title:
--   State $(x_{t+1},u_t)$ of the Conic Blackwell Algorithm Plus (CBA$^+$, Algorithm 1)
-- statement:
--   Fix a convex compact decision set $\mathcal X\subset\mathbb R^n$ with $\kappa=\max_{x\in\mathcal X}\|x\|_2$, the cone $\mathcal C=\operatorname{cone}(\{\kappa\}\times\mathcal X)\subset\mathbb R^{n+1}$, a point $x_0\in\mathcal X$ used by CHOOSEDECISION, an initial decision $x_1\in\mathcal X$, payoff weights $(\omega_t)_{t\ge1}$ and losses $(f_t)_{t\ge1}$ in $\mathbb R^n$. The instantaneous payoff of round $t$ is $v_t=(\langle f_t,x_t\rangle/\kappa,\,-f_t)$.
--
--   CBA$^+$ starts from $u_0=0$ and, for $t=0,1,2,\dots$,
--
--   1. observes $f_{t+1}$ and updates $u_{t+1}=\mathrm{UPDATEPAYOFF}_{\mathrm{CBA}^+}(u_t,x_{t+1},f_{t+1},\omega_{t+1})=\pi_{\mathcal C}\big(u_t+\omega_{t+1}v_{t+1}\big)$;
--   2. chooses $x_{t+2}=\mathrm{CHOOSEDECISION}_{\mathrm{CBA}^+}(u_{t+1})$.
--
--   This definition is the map $t\mapsto(x_{t+1},u_t)$.
--
--   **Formalization Note** Rounds are numbered from $1$; $\omega_0$ and $f_0$ are never used. $\pi_{\mathcal C}$ is the published `PerspEpi.projC`, the unique nearest point; it exists because $\mathcal C$ is nonempty, closed and convex, so the fallback value of `projC` is never used. Algorithm 1, line 4, prints $u_1=\omega_1v_1$ without projecting; here $u_1=\pi_{\mathcal C}(\omega_1v_1)$, the update rule applied to $u_0=0$. The two agree whenever $\omega_1v_1\in\mathcal C$, and the printed one can leave $\mathcal C$ (for $\mathcal X=[-1,1]$, $x_1=1/10$, $f_1=1$, $\omega_1=1$ it gives $u_1=(1/10,-1)$ and then $x_2=-10\notin\mathcal X$), contradicting the paper's statement on p.5 that $u\in\mathcal C$ always holds.
-- source:
--   Grand-Clément & Kroer, Solving Optimization Problems with Blackwell Approachability, arXiv:2202.12277v1 (https://arxiv.org/abs/2202.12277v1), Algorithm 1, p.6; UPDATEPAYOFF and CHOOSEDECISION, p.5

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_AlgorithmOne
import Definitions.Def_PerspEpi_projC
import Definitions.Def_ConicBlackwell_chooseDecision
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace ConicBlackwell

/-- **The state of a CBA+ run** (Algorithm 1, p.6, with UPDATEPAYOFF_{CBA+}, p.5):
`cbaPlusState X x₀ x₁ ω f t = (x_{t+1}, u_t)`.
Grand-Clément & Kroer, *Solving Optimization Problems with Blackwell Approachability*, arXiv:2202.12277v1, Algorithm 1, p.6; §3.1, p.5.

The run starts from `u₀ = 0` and the first decision `x₁`.  Round `t + 1` observes the loss
`f (t + 1)`, forms the payoff `v_{t+1} = (⟨f_{t+1}, x_{t+1}⟩/κ, −f_{t+1})`, sets
`u_{t+1} = UPDATEPAYOFF_{CBA+}(u_t, x_{t+1}, f_{t+1}, ω_{t+1}) = π_C(u_t + ω_{t+1} v_{t+1})` with
`C = cone({κ} × X)`, and chooses `x_{t+2} = CHOOSEDECISION_{CBA+}(u_{t+1})`.

Formalization Note: rounds are numbered from `1`; `ω 0` and `f 0` are never used.  Line 4 of
Algorithm 1 prints `u₁ = ω₁ v₁` without the projection; here `u₁ = π_C(ω₁ v₁)` (the update rule
applied to `u₀ = 0`).  `π_C` is `PerspEpi.projC`, the unique nearest point (its fallback value
is never used: `C` is nonempty, closed and convex for nonempty compact convex `X`).  The two agree whenever `ω₁ v₁ ∈ C`; without the projection `u₁ ∉ C` is
possible, contradicting the paper's "we always have u ∈ C" (p.5). -/
noncomputable def cbaPlusState {n : ℕ} (X : Set (E n)) (x₀ x₁ : E n) (ω : ℕ → ℝ)
    (f : ℕ → E n) : ℕ → E n × E (n + 1)
  | 0 => (x₁, 0)
  | t + 1 =>
      let p := cbaPlusState X x₀ x₁ ω f t
      let u := PerspEpi.projC (cone (lift (kappa X) '' X)) (p.2 + ω (t + 1) • payoff X p.1 (f (t + 1)))
      (chooseDecision X x₀ u, u)

end ConicBlackwell


