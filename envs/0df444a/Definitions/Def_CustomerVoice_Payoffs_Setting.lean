-- Prove2me | Definitions.Def_CustomerVoice_Payoffs_Setting
-- name    : CustomerVoice_Payoffs_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:13.006362+00:00
-- url     : https://prove2.me/theorems/da751068-2bb9-4824-800d-03b24f105564
-- title:
--   §2 and §§3.2–3.4 — two-type customization model, equilibrium qualities, and payoffs
-- statement:
--   A seller serves high- and low-preference buyers with quality values $\theta_H>\theta_L>0$. The high type has population weight $\alpha$ and the low type has weight $1-\alpha$. The seller has bargaining weight $\gamma$, production-cost coefficient $k$, and selling-cost coefficient $s$, with $0<\alpha,\gamma<1$ and $k,s>0$.
--
--   The seller's payoff from quality $q$ when it believes the buyer's type is $\hat\theta$ is
--   $$v(q,\hat\theta)=\gamma(\hat\theta q-kq^2)-sq^2.$$
--   The buyer payoff at an A-Learning design and the O-Learning request payoff both retain the two nonnegative-part terms of the paper's equations (5) and (9). Their argument order follows the respective equations.
--
--   For $i\in\{H,L\}$, the equilibrium qualities are $q^A_i=\gamma\theta_i/(2s+2\gamma k)$ and $q^O_i=\min\{\gamma\theta_i/(s+\gamma k),\theta_i/(2k)\}$. Seller payoffs $V^A,V^O$ average $v(q^A_i,\theta_i)$ and $v(q^O_i,\theta_i)$ using the two population weights. Buyer payoffs $U^A_i,U^O_i$ evaluate equations (5) and (9) at the corresponding truthful type and quality. These definitions support the four payoff comparisons in Proposition 8.
--
--   **Formalization Note** `thH`, `thL`, `alpha`, and `gamma` represent $\theta_H$, $\theta_L$, $\alpha$, and $\gamma$. The price-setting stage is represented by the reduced-form payoff equations. Missions I and II characterize the displayed qualities as equilibrium outcomes; this mission uses those expressions as definitions of the payoffs being compared.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), pp. 5–6, 12, 15–16, 20, 23, §2, (4)–(5), (8)–(9), (13), Proposition 8

import Mathlib
import Definitions.Def_CustomerVoice_ALearn_Setting

namespace CustomerVoice.Payoffs

instance : Fintype CustomerVoice.ALearn.BType where
  elems := {CustomerVoice.ALearn.BType.H, CustomerVoice.ALearn.BType.L}
  complete := by
    intro t
    cases t <;> simp

structure Model where
  thH : ℝ
  thL : ℝ
  alpha : ℝ
  gamma : ℝ
  k : ℝ
  s : ℝ

def Model.theta (M : Model) : CustomerVoice.ALearn.BType → ℝ
  | .H => M.thH
  | .L => M.thL

def Model.alphaW (M : Model) : CustomerVoice.ALearn.BType → ℝ
  | .H => M.alpha
  | .L => 1 - M.alpha

def Model.Standing (M : Model) : Prop :=
  M.thL > 0 ∧ M.thH > M.thL ∧
  0 < M.alpha ∧ M.alpha < 1 ∧
  0 < M.gamma ∧ M.gamma < 1 ∧
  0 < M.k ∧ 0 < M.s

def Model.v (M : Model) (q thHat : ℝ) : ℝ :=
  M.gamma * (thHat * q - M.k * q ^ 2) - M.s * q ^ 2

def Model.uA (M : Model) (th thHat q : ℝ) : ℝ :=
  M.gamma * max (th * q - thHat * q) 0 +
    (1 - M.gamma) * max (th * q - M.k * q ^ 2) 0

def Model.mu (M : Model) (q th thHat : ℝ) : ℝ :=
  M.gamma * max (th * q - thHat * q) 0 +
    (1 - M.gamma) * max (th * q - M.k * q ^ 2) 0

noncomputable def Model.qA (M : Model) (t : CustomerVoice.ALearn.BType) : ℝ :=
  M.gamma * M.theta t / (2 * M.s + 2 * M.gamma * M.k)

noncomputable def Model.qO (M : Model) (t : CustomerVoice.ALearn.BType) : ℝ :=
  min (M.gamma * M.theta t / (M.s + M.gamma * M.k))
    (M.theta t / (2 * M.k))

noncomputable def Model.VA (M : Model) : ℝ :=
  ∑ t : CustomerVoice.ALearn.BType, M.alphaW t * M.v (M.qA t) (M.theta t)

noncomputable def Model.VO (M : Model) : ℝ :=
  ∑ t : CustomerVoice.ALearn.BType, M.alphaW t * M.v (M.qO t) (M.theta t)

noncomputable def Model.UA (M : Model) (t : CustomerVoice.ALearn.BType) : ℝ :=
  M.uA (M.theta t) (M.theta t) (M.qA t)

noncomputable def Model.UO (M : Model) (t : CustomerVoice.ALearn.BType) : ℝ :=
  M.mu (M.qO t) (M.theta t) (M.theta t)

def Model.withS (M : Model) (s' : ℝ) : Model := { M with s := s' }

end CustomerVoice.Payoffs


