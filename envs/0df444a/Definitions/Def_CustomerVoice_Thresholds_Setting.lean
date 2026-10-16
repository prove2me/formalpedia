-- Prove2me | Definitions.Def_CustomerVoice_Thresholds_Setting
-- name    : CustomerVoice_Thresholds_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:09.596687+00:00
-- url     : https://prove2.me/theorems/0ba9ec1c-c2f9-4e9c-84ed-36b965b5b6f1
-- title:
--   Propositions 1 and 3 — the model primitives and the critical values Δ_H, Δ_L, Δ (A-Learning) and Λ_{H1}, Λ_{H2}, Λ_L, Λ (O-Learning)
-- statement:
--   This file fixes the primitives of Guo's two-type customization model and the two **critical values** of the type ratio $\theta_H/\theta_L$ that the paper compares.
--
--   A **model** consists of six real numbers $(\theta_H,\theta_L,\alpha,\gamma,k,s)$: the quality preferences $\theta_H$ and $\theta_L$ of the high and the low buyer type, the prior share $\alpha$ of high-type buyers, the seller's bargaining power $\gamma$ (the probability that the seller makes the take-it-or-leave-it price offer), the production-cost coefficient $k$ (a product of quality $q$ costs $kq^2$) and the selling-cost coefficient $s$ (selling it costs $sq^2$). The paper's **standing assumptions** (§2) are
--   $$\theta_H>\theta_L>0,\qquad \alpha\in(0,1),\qquad \gamma\in(0,1),\qquad k>0,\qquad s>0 .$$
--
--   The **A-Learning thresholds** (Proposition 1 and p. 13) are
--   $$\Delta_H=\frac{\gamma[2s+(1+\gamma)k]}{(1-\gamma)(2s+\gamma k)},\qquad \Delta_L=\frac{2s+\gamma k}{\gamma k},\qquad \Delta=\max\{\Delta_H,\Delta_L\}.$$
--
--   The **O-Learning thresholds** (Proposition 3) are
--   $$\Lambda_{H1}=\frac{\gamma(s+k)}{(1-\gamma)s},\qquad \Lambda_{H2}=\frac{1+\gamma}{1-\gamma},\qquad \Lambda_L=\frac{s}{\gamma k},\qquad \Lambda=\max\{\min\{\Lambda_{H1},\Lambda_{H2}\},\Lambda_L\}.$$
--
--   In the paper, Proposition 1 shows that informative cheap-talk communication under A-Learning is an equilibrium if and only if $\theta_H/\theta_L\ge\Delta$, and Proposition 3 shows that the cheap-signaling separating equilibrium under O-Learning exists if and only if $\theta_H/\theta_L\ge\Lambda$; this is why $\Delta$ and $\Lambda$ are called critical values. Here they are defined directly by the printed closed-form expressions; the two games are not part of this file.
--
--   **Formalization Note** The thresholds are functions of a structure `Model` holding the six primitives; `Model.Standing` collects the standing assumptions. Only $\gamma$, $k$ and $s$ enter the thresholds; $\theta_H$, $\theta_L$ and $\alpha$ are kept so that the model is the paper's. Under the standing assumptions every denominator ($1-\gamma$, $2s+\gamma k$, $s$, $\gamma k$) is positive, so Lean's convention $x/0=0$ never applies.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), pp. 5–6, §2 (standing assumptions); p. 12, Proposition 1 (Δ); p. 13 (Δ_H, Δ_L); p. 17, Proposition 3 (Λ_{H1}, Λ_{H2}, Λ_L, Λ)

import Mathlib

namespace CustomerVoice.Thresholds

structure Model where
  θH : ℝ
  θL : ℝ
  α : ℝ
  γ : ℝ
  k : ℝ
  s : ℝ

def Model.Standing (M : Model) : Prop :=
  0 < M.θL ∧ M.θL < M.θH ∧
  0 < M.α ∧ M.α < 1 ∧
  0 < M.γ ∧ M.γ < 1 ∧
  0 < M.k ∧ 0 < M.s

noncomputable def Model.DeltaH (M : Model) : ℝ :=
  M.γ * (2 * M.s + (1 + M.γ) * M.k) / ((1 - M.γ) * (2 * M.s + M.γ * M.k))

noncomputable def Model.DeltaL (M : Model) : ℝ :=
  (2 * M.s + M.γ * M.k) / (M.γ * M.k)

noncomputable def Model.Delta (M : Model) : ℝ :=
  max M.DeltaH M.DeltaL

noncomputable def Model.LambdaH1 (M : Model) : ℝ :=
  M.γ * (M.s + M.k) / ((1 - M.γ) * M.s)

noncomputable def Model.LambdaH2 (M : Model) : ℝ :=
  (1 + M.γ) / (1 - M.γ)

noncomputable def Model.LambdaL (M : Model) : ℝ :=
  M.s / (M.γ * M.k)

noncomputable def Model.Lambda (M : Model) : ℝ :=
  max (min M.LambdaH1 M.LambdaH2) M.LambdaL

end CustomerVoice.Thresholds


