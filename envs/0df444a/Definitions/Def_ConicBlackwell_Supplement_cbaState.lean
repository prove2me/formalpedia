-- Prove2me | Definitions.Def_ConicBlackwell_Supplement_cbaState
-- name    : ConicBlackwell_Supplement_cbaState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:45:18.004849+00:00
-- url     : https://prove2.me/theorems/4a8b00cc-970b-4c30-b5c4-fda58d2b430a
-- title:
--   State $(x_{t+1},u_t)$ of the Conic Blackwell Algorithm (CBA) with payoff weights
-- statement:
--   Fix a convex compact decision set $\mathcal X\subset\mathbb R^n$ with $\kappa=\max_{x\in\mathcal X}\|x\|_2$, the cone $\mathcal C=\operatorname{cone}(\{\kappa\}\times\mathcal X)\subset\mathbb R^{n+1}$, a point $x_0\in\mathcal X$ used by CHOOSEDECISION, an initial decision $x_1\in\mathcal X$, payoff weights $(\omega_t)_{t\ge1}$ and losses $(f_t)_{t\ge1}$ in $\mathbb R^n$. The instantaneous payoff of round $t$ is $v_t=(\langle f_t,x_t\rangle/\kappa,\,-f_t)$.
--
--   The **Conic Blackwell Algorithm** (CBA) of Abernethy, Bartlett and Hazan, with payoff weights, starts from $u_0=0$ and, for $t=0,1,2,\dots$,
--
--   1. observes $f_{t+1}$ and updates $u_{t+1}=\mathrm{UPDATEPAYOFF}_{\mathrm{CBA}}(u_t,x_{t+1},f_{t+1},\omega_{t+1})=u_t+\omega_{t+1}v_{t+1}$ (no projection);
--   2. chooses $x_{t+2}=\mathrm{CHOOSEDECISION}_{\mathrm{CBA}}(u_{t+1})=\mathrm{CHOOSEDECISION}_{\mathrm{CBA}^+}\big(\pi_{\mathcal C}(u_{t+1})\big)$.
--
--   This definition is the map $t\mapsto(x_{t+1},u_t)$. In particular $u_t=\sum_{\tau=1}^t\omega_\tau v_\tau$. CBA differs from CBA$^+$ exactly as regret matching differs from regret matching$^+$: CBA$^+$ projects the aggregate payoff in the update, CBA only when choosing the decision.
--
--   **Formalization Note** Rounds are numbered from $1$; $\omega_0$ and $f_0$ are never used. $\pi_{\mathcal C}$ is the published `PerspEpi.projC`, the unique nearest point (it exists because $\mathcal C$ is nonempty, closed and convex); CHOOSEDECISION$_{\mathrm{CBA}^+}$ is the published `ConicBlackwell.chooseDecision`.
-- source:
--   Grand-Clément & Kroer, Solving Optimization Problems with Blackwell Approachability, arXiv:2202.12277v1 (https://arxiv.org/abs/2202.12277v1), §3.1, p.6 (UPDATEPAYOFF_CBA, CHOOSEDECISION_CBA); Algorithm 1, p.6 (loop); identity u_t = Σ ω_τ v_τ, p.7

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_AlgorithmOne
import Definitions.Def_PerspEpi_projC
import Definitions.Def_ConicBlackwell_chooseDecision
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace ConicBlackwell.Supplement

/-- **The state of a CBA run** (the Conic Blackwell Algorithm of Abernethy, Bartlett & Hazan 2011,
with payoff weights), `cbaState X x₀ x₁ ω f t = (x_{t+1}, u_t)`.
Grand-Clément & Kroer, *Solving Optimization Problems with Blackwell Approachability*,
arXiv:2202.12277v1, §3.1, p.6 (UPDATEPAYOFF_{CBA} and CHOOSEDECISION_{CBA}); Algorithm 1, p.6, for
the loop.

The run starts from `u₀ = 0` and the first decision `x₁`.  Round `t + 1` observes the loss
`f (t + 1)`, forms the payoff `v_{t+1} = (⟨f_{t+1}, x_{t+1}⟩/κ, −f_{t+1})`, sets
`u_{t+1} = UPDATEPAYOFF_{CBA}(u_t, x_{t+1}, f_{t+1}, ω_{t+1}) = u_t + ω_{t+1} v_{t+1}` (no projection),
and chooses `x_{t+2} = CHOOSEDECISION_{CBA}(u_{t+1}) = CHOOSEDECISION_{CBA+}(π_C(u_{t+1}))` with
`C = cone({κ} × X)`.  Hence `u_t = Σ_{τ=1}^t ω_τ v_τ` (p.7).

Formalization Note: rounds are numbered from `1`; `ω 0` and `f 0` are never used.  `π_C` is
`PerspEpi.projC`, the unique nearest point (its fallback value is never used: `C` is nonempty,
closed and convex for nonempty compact convex `X`); CHOOSEDECISION_{CBA+} is the published
`ConicBlackwell.chooseDecision` with the arbitrary point `x₀`. -/
noncomputable def cbaState {n : ℕ} (X : Set (E n)) (x₀ x₁ : E n) (ω : ℕ → ℝ)
    (f : ℕ → E n) : ℕ → E n × E (n + 1)
  | 0 => (x₁, 0)
  | t + 1 =>
      let p := cbaState X x₀ x₁ ω f t
      let u := p.2 + ω (t + 1) • payoff X p.1 (f (t + 1))
      (ConicBlackwell.chooseDecision X x₀ (PerspEpi.projC (cone (lift (kappa X) '' X)) u), u)

end ConicBlackwell.Supplement


