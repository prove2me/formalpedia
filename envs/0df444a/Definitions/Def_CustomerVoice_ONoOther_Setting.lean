-- Prove2me | Definitions.Def_CustomerVoice_ONoOther_Setting
-- name    : CustomerVoice_ONoOther_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:06.745015+00:00
-- url     : https://prove2.me/theorems/6eb71207-b5bb-487c-8627-5148808369eb
-- title:
--   §2 and §3.3 — two-type O-Learning customization game, payoffs (9), acceptance, separating equilibrium, and Λ
-- statement:
--   A buyer privately knows whether its quality preference is $\theta_H$ or $\theta_L$, with $\theta_H>\theta_L>0$ and prior probability $\alpha\in(0,1)$ of the high type. The seller makes the price offer with probability $\gamma\in(0,1)$; the buyer makes it otherwise. Production and selling costs for quality $q\ge0$ are $kq^2$ and $sq^2$, with $k,s>0$.
--
--   Conditional on acceptance, a buyer with true preference $\theta$ facing seller perception $\hat\theta$ receives
--   $$
--   \mu(q,\theta,\hat\theta)=\gamma\max\{\theta q-\hat\theta q,0\}+(1-\gamma)\max\{\theta q-kq^2,0\}.
--   $$
--   The seller accepts exactly when $\gamma(\hat\theta q-kq^2)-sq^2\ge0$; a rejected request pays the buyer zero. A separating pure-strategy equilibrium is a pair of distinct nonnegative requests $q_H,q_L$ and a belief function on all real requests. Beliefs identify the types at their equilibrium requests, and each type's request maximizes its payoff against every nonnegative deviation. Off-path beliefs are unrestricted.
--
--   The complete-information request is $q^*(\theta)=\min\{\gamma\theta/(s+\gamma k),\theta/(2k)\}$. Define $\Lambda_{H1}=\gamma(s+k)/((1-\gamma)s)$, $\Lambda_{H2}=(1+\gamma)/(1-\gamma)$, $\Lambda_L=s/(\gamma k)$, and $\Lambda=\max\{\min(\Lambda_{H1},\Lambda_{H2}),\Lambda_L\}$. These expressions fix the game and threshold used by every theorem in this mission.
--
--   **Formalization Note** The two types are named constructors. The prior is retained as a standing assumption although this equilibrium result does not depend on it. The pricing stage enters through the reduced-form payoff. The seller accepts at equality, as the paper states.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), pp. 5–9 and 16–17, §2, §3.3, (1), (9)–(10), Proposition 3

import Mathlib
import Definitions.Def_CustomerVoice_ALearn_Setting

namespace CustomerVoice.ONoOther

structure Model where
  θH : ℝ
  θL : ℝ
  α : ℝ
  γ : ℝ
  k : ℝ
  s : ℝ

def Model.θ (M : Model) : CustomerVoice.ALearn.BType → ℝ
  | .H => M.θH
  | .L => M.θL

def Model.Standing (M : Model) : Prop :=
  0 < M.θL ∧ M.θL < M.θH ∧
  0 < M.α ∧ M.α < 1 ∧
  0 < M.γ ∧ M.γ < 1 ∧
  0 < M.k ∧ 0 < M.s

noncomputable def Model.mu (M : Model) (q θ θh : ℝ) : ℝ :=
  M.γ * max (θ * q - θh * q) 0 +
    (1 - M.γ) * max (θ * q - M.k * q ^ 2) 0

def Model.accepts (M : Model) (θh q : ℝ) : Prop :=
  0 ≤ M.γ * (θh * q - M.k * q ^ 2) - M.s * q ^ 2

noncomputable def Model.pay (M : Model) (bel : ℝ → CustomerVoice.ALearn.BType) (t : CustomerVoice.ALearn.BType)
    (q : ℝ) : ℝ := by
  classical
  exact if M.accepts (M.θ (bel q)) q then M.mu q (M.θ t) (M.θ (bel q)) else 0

def Model.OSepEq (M : Model) (req : CustomerVoice.ALearn.BType → ℝ) (bel : ℝ → CustomerVoice.ALearn.BType) : Prop :=
  (∀ t : CustomerVoice.ALearn.BType, 0 ≤ req t) ∧
  req .H ≠ req .L ∧
  (∀ t : CustomerVoice.ALearn.BType, bel (req t) = t) ∧
  (∀ t : CustomerVoice.ALearn.BType, ∀ q : ℝ, 0 ≤ q → M.pay bel t q ≤ M.pay bel t (req t))

noncomputable def Model.qStar (M : Model) (θ : ℝ) : ℝ :=
  min (M.γ * θ / (M.s + M.γ * M.k)) (θ / (2 * M.k))

noncomputable def Model.LambdaH1 (M : Model) : ℝ :=
  M.γ * (M.s + M.k) / ((1 - M.γ) * M.s)

noncomputable def Model.LambdaH2 (M : Model) : ℝ :=
  (1 + M.γ) / (1 - M.γ)

noncomputable def Model.LambdaL (M : Model) : ℝ :=
  M.s / (M.γ * M.k)

noncomputable def Model.Lambda (M : Model) : ℝ :=
  max (min M.LambdaH1 M.LambdaH2) M.LambdaL

end CustomerVoice.ONoOther


