-- Prove2me | Definitions.Def_ReedGGN_RenewalRep_Equations
-- name    : ReedGGN_RenewalRep_Equations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:50.812378+00:00
-- url     : https://prove2.me/theorems/59bf747a-fe82-4e21-81c4-f69194434e1c
-- title:
--   The diffusion-limit equation (5.33) and the renewal-function equation (5.41), for one sample path
-- statement:
--   Fix a service-time law $\mu$ with distribution function $F$, its equilibrium distribution $F_e$ (5.4), its renewal measure $dM$, a constant $\beta\in\mathbb R$ (the Halfin–Whitt parameter of (5.3)) and a driving path $\zeta$ (in the paper, $\tilde\zeta=\tilde M_Q+\tilde Q_I$ of (5.40)). For a real number $y$ write $y^+=\max(y,0)$ and $y^-=\min(y,0)\le 0$.
--
--   1. A path $q$ **solves the limit equation (5.33)** if
--   $$q(t)=\zeta(t)-\beta F_e(t)+\int_0^t q^+(t-s)\,dF(s)\qquad\text{for every } t\ge 0.$$
--   2. A path $q$ **solves the renewal-function equation (5.41)** if
--   $$q(t)=\zeta(t)+\int_0^t\zeta(t-u)\,dM(u)-\beta t-\int_0^t q^-(t-u)\,dM(u)\qquad\text{for every } t\ge 0.$$
--
--   Equation (5.33) is the expanded form of the diffusion limit of Theorem 5.1; Corollary 5.2 shows that the two equations have the same càdlàg solutions.
--
--   **Formalization Note** Both Stieltjes integrals are Lebesgue integrals over the **closed** interval $[0,t]$ (against $\mu$, respectively $dM$), so atoms at $0$ are included. $q^-$ is $\min(q,0)$, the paper's convention on p. 29, not Mathlib's `negPart` $=\max(-q,0)$. The integrals are Bochner integrals, which return $0$ on non-integrable integrands; every theorem of the mission applies these equations only to càdlàg $q$ and $\zeta$, which are bounded and measurable on $[0,t]$.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 25, Eq. (5.33); p. 29, Eqs. (5.40)–(5.41)

import Mathlib
import Definitions.Def_ReedGGN_RenewalRep_Basic
import Definitions.Def_ReedGGN_RenewalRep_RenewalFunction

namespace ReedGGN.RenewalRep

open MeasureTheory

/-- The diffusion-limit equation (5.33), p. 25, for one sample path: with the driving path
`ζ = M̃_Q + Q̃_I` (5.40) and the Halfin–Whitt constant `β`,
`q(t) = ζ(t) − β F_e(t) + ∫_{[0,t]} q⁺(t − s) dF(s)` for every `t ≥ 0`,
where `q⁺ = max(q, 0)` and the integral is over the closed interval `[0, t]` against `μ`. -/
def SolvesLimitEq (μ : Measure ℝ) (ζ : ℝ → ℝ) (β : ℝ) (q : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → q t = ζ t - β * ReedGGN.Regulator.Fe μ t + ∫ s in Set.Icc 0 t, max (q (t - s)) 0 ∂μ

/-- The renewal-function equation (5.41), p. 29, for one sample path:
`q(t) = ζ(t) + ∫_{[0,t]} ζ(t − u) dM(u) − β t − ∫_{[0,t]} q⁻(t − u) dM(u)` for every `t ≥ 0`,
where `q⁻ = min(q, 0) ≤ 0` (the paper's convention) and `dM` is `renewalMeasure μ`. -/
def SolvesRenewalEq (μ : Measure ℝ) (ζ : ℝ → ℝ) (β : ℝ) (q : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → q t = ζ t + (∫ u in Set.Icc 0 t, ζ (t - u) ∂(renewalMeasure μ)) - β * t
    - ∫ u in Set.Icc 0 t, min (q (t - u)) 0 ∂(renewalMeasure μ)

end ReedGGN.RenewalRep


