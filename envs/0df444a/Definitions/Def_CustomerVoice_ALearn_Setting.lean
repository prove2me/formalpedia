-- Prove2me | Definitions.Def_CustomerVoice_ALearn_Setting
-- name    : CustomerVoice_ALearn_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T23:12:23.166361+00:00
-- url     : https://prove2.me/theorems/d209352c-75d6-44e0-9c01-886b2f58de40
-- title:
--   §2 and §3.2 — two-type A-Learning model, payoffs, thresholds and separating equilibrium
-- statement:
--   A buyer privately knows whether its preference for product quality is high or low. Write the two preferences as $\theta_H>\theta_L>0$, the high-type share as $\alpha\in(0,1)$, the seller's chance of making the price offer as $\gamma\in(0,1)$, the production-cost coefficient as $k>0$, and the selling-cost coefficient as $s>0$. Quality satisfies $q\geq0$. The two cost components are $kq^2$ and $sq^2$.
--
--   If the seller believes the buyer's preference is $\hat\theta$, its expected payoff from quality $q$ is
--   $$v(q,\hat\theta)=\gamma(\hat\theta q-kq^2)-sq^2.$$
--   A buyer whose actual preference is $\theta$ receives, at a given design $q$,
--   $$u_A(\theta,\hat\theta,q)=\gamma\max\{\theta q-\hat\theta q,0\}+(1-\gamma)\max\{\theta q-kq^2,0\}.$$
--   The paper's closed-form optimal design is $q(\hat\theta)=\gamma\hat\theta/(2s+2\gamma k)$, and its payoff notation is $u(\theta,\hat\theta)=u_A(\theta,\hat\theta,q(\hat\theta))$. The high and low incentive conditions compare truthful reporting with imitating the other type. The thresholds are
--   $$\Delta_H=\frac{\gamma[2s+(1+\gamma)k]}{(1-\gamma)(2s+\gamma k)},\qquad \Delta_L=\frac{2s+\gamma k}{\gamma k},\qquad \Delta=\max\{\Delta_H,\Delta_L\}.$$
--
--   An informative equilibrium consists of two distinct cheap-talk messages, a message rule that separates the two types, seller beliefs that identify each type on its chosen message, a nonnegative design that maximizes the seller's payoff at each message, and a message choice that maximizes each buyer type's payoff against both possible messages. The definition is the common model for Proposition 1 and its supporting results.
--
--   **Formalization Note** The pricing stage is represented by the printed payoff formulas rather than a separate bargaining game. Both messages are on path because there are exactly two and the message rule separates the types. The closed form $q(\hat\theta)$ is used in the paper's incentive conditions; the equilibrium design itself is required to attain the seller's maximum over $q\geq0$.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), pp. 5–12, §2, (1), (4)–(7), Proposition 1

import Mathlib

namespace CustomerVoice.ALearn

/-- The two privately known buyer types in §2. -/
inductive BType where
  | H
  | L
  deriving DecidableEq

/-- The two distinct cheap-talk messages allowed for a separating equilibrium in §2. -/
inductive Msg where
  | mH
  | mL
  deriving DecidableEq

/-- The primitives of the customization model in §2. -/
structure Model where
  θH : ℝ
  θL : ℝ
  α : ℝ
  γ : ℝ
  k : ℝ
  s : ℝ

namespace Model

/-- The standing assumptions of §2, pp. 5–6. -/
structure Standing (M : Model) : Prop where
  θL_pos : 0 < M.θL
  θH_gt_θL : M.θL < M.θH
  α_pos : 0 < M.α
  α_lt_one : M.α < 1
  γ_pos : 0 < M.γ
  γ_lt_one : M.γ < 1
  k_pos : 0 < M.k
  s_pos : 0 < M.s

/-- The preference for quality of a buyer type. -/
def θ (M : Model) : BType → ℝ
  | .H => M.θH
  | .L => M.θL

/-- Seller payoff at quality `q` under belief `θh`, equation (4). -/
def v (M : Model) (q θh : ℝ) : ℝ :=
  M.γ * (θh * q - M.k * q ^ 2) - M.s * q ^ 2

/-- Buyer payoff at a given quality, equation (5) before substituting the optimal design. -/
def uA (M : Model) (θtrue θh q : ℝ) : ℝ :=
  M.γ * max (θtrue * q - θh * q) 0 +
    (1 - M.γ) * max (θtrue * q - M.k * q ^ 2) 0

/-- The closed-form design printed after equation (4). -/
noncomputable def qOpt (M : Model) (θh : ℝ) : ℝ :=
  M.γ * θh / (2 * M.s + 2 * M.γ * M.k)

/-- The buyer payoff in equation (5), with the seller's printed optimal design. -/
noncomputable def u (M : Model) (θtrue θh : ℝ) : ℝ :=
  M.uA θtrue θh (M.qOpt θh)

/-- The high-type threshold on p. 13. -/
noncomputable def DeltaH (M : Model) : ℝ :=
  M.γ * (2 * M.s + (1 + M.γ) * M.k) /
    ((1 - M.γ) * (2 * M.s + M.γ * M.k))

/-- The low-type threshold on p. 13. -/
noncomputable def DeltaL (M : Model) : ℝ :=
  (2 * M.s + M.γ * M.k) / (M.γ * M.k)

/-- The threshold in Proposition 1, p. 12. -/
noncomputable def Delta (M : Model) : ℝ := max M.DeltaH M.DeltaL

/-- Incentive condition (6), p. 12. -/
def ICH (M : Model) : Prop := M.u M.θH M.θL ≤ M.u M.θH M.θH

/-- Incentive condition (7), p. 12. -/
def ICL (M : Model) : Prop := M.u M.θL M.θH ≤ M.u M.θL M.θL

/-- A separating perfect Bayesian equilibrium of the A-Learning cheap-talk game.
The seller's design is an attained maximum over nonnegative qualities; every buyer type
must prefer its own message to every available message. -/
def SepEq (M : Model) (m : BType → Msg) (bel : Msg → BType)
    (d : Msg → ℝ) : Prop :=
  m .H ≠ m .L ∧
    (∀ t : BType, bel (m t) = t) ∧
    (∀ x : Msg, 0 ≤ d x ∧
      IsMaxOn (fun q : ℝ => M.v q (M.θ (bel x))) (Set.Ici 0) (d x)) ∧
    (∀ t : BType, ∀ x : Msg,
      M.uA (M.θ t) (M.θ (bel x)) (d x) ≤
        M.uA (M.θ t) (M.θ (bel (m t))) (d (m t)))

/-- Existence of an informative equilibrium, the subject of Proposition 1. -/
def InformativeEq (M : Model) : Prop :=
  ∃ (m : BType → Msg) (bel : Msg → BType) (d : Msg → ℝ), M.SepEq m bel d

end Model

end CustomerVoice.ALearn


