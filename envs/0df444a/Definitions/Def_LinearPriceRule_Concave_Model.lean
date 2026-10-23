-- Prove2me | Definitions.Def_LinearPriceRule_Concave_Model
-- name    : LinearPriceRule_Concave_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:24.202722+00:00
-- url     : https://prove2.me/theorems/692cbb88-ffc7-421e-adf4-95c0cc9872a3
-- title:
--   §1.4, §2, pp. 4–8, 26 — pricing with an unknown inverse demand: P_A on [0, Q_max], profit, optimal quantity, the linear price (P_m + c)/2, demand Q_A and the rule's profit Π*
-- statement:
--   This file fixes the model of a single-product monopoly that knows its marginal cost and its maximum price but not its demand curve.
--
--   A **market** consists of a maximum price $P_m$, a constant marginal cost $c$, a market-saturation quantity $Q_{\max}$, and the actual inverse demand $P_A(Q)$: the price at which exactly $Q$ units are demanded. The **standing assumptions** are
--   $$
--   0 \le c < P_m, \qquad 0 < Q_{\max}, \qquad P_A(0) = P_m,
--   $$
--   and $P_A$ is non-increasing and continuous on $[0, Q_{\max}]$. Quantities beyond $Q_{\max}$ are never sold: the market saturates there.
--
--   The derived objects are:
--
--   1. the **profit** of selling $Q$ units at the market-clearing price, $\Pi(Q) = (P_A(Q) - c)\,Q$;
--   2. an **optimal quantity** $Q^{**}$: a point of $[0, Q_{\max}]$ maximizing $\Pi$ there; the optimal price is $P^{**} = P_A(Q^{**})$ and the maximum profit $\Pi^{**} = \Pi(Q^{**})$;
--   3. the **linear price** $P^* = (P_m + c)/2$, the optimal price for a linear demand through $(0, P_m)$;
--   4. the **demand at price** $p$, $Q_A(p) = \sup\{Q \in [0, Q_{\max}] : P_A(Q) \ge p\}$, the largest quantity sold at price $p$;
--   5. the **profit of the linear rule**, $\Pi^* = (P^* - c)\,Q_A(P^*)$, the profit of charging $P^*$;
--   6. for a linear inverse demand $P(Q) = P_m - bQ$, the profit $(P_m - bQ - c)\,Q$ at quantity $Q$.
--
--   These objects are shared by every statement of the mission: Theorem 1, Proposition 5 and the remarks around them compare $P^{**}$ with $P^*$ and $\Pi^{**}$ with $\Pi^*$.
--
--   **Formalization Note** $P_A$ is a function $\mathbb R \to \mathbb R$ whose values outside $[0, Q_{\max}]$ are never used: optimality and $Q_A$ range over $[0, Q_{\max}]$ only, and monotonicity and continuity are assumed there only. Nonnegativity of $P_A$ is not assumed (no statement uses it). $Q_A(p)$ is an `sSup`; for $p \le P_m$ the set contains $0$ and is bounded by $Q_{\max}$, and under continuity the supremum is attained. Optimality is over quantities; the optimal price is read off as $P_A(Q^{**})$.
-- source:
--   Cohen, Perakis & Pindyck, SSRN 2673810, pp. 4–8, 26, §1.4 eq. (1), §2, proof of Proposition 5

import Mathlib

namespace LinearPriceRule.Concave

/-- A single-product monopoly market (Cohen, Perakis & Pindyck, §1.4, §2, pp. 4–8):
maximum price `Pm` (P_m), constant marginal cost `c`, market saturation quantity `Qmax`
(Q_max), and the actual inverse demand `PA` (P_A(Q)), which is only read on `[0, Qmax]`. -/
structure Market where
  Pm : ℝ
  c : ℝ
  Qmax : ℝ
  PA : ℝ → ℝ

/-- Standing assumptions on a market: `0 ≤ c < P_m`, `0 < Q_max`, `P_A(0) = P_m`, and
`P_A` non-increasing and continuous on `[0, Q_max]`. -/
structure Market.Standing (M : Market) : Prop where
  c_nonneg : 0 ≤ M.c
  c_lt_Pm : M.c < M.Pm
  Qmax_pos : 0 < M.Qmax
  PA_zero : M.PA 0 = M.Pm
  antitone : AntitoneOn M.PA (Set.Icc 0 M.Qmax)
  continuous : ContinuousOn M.PA (Set.Icc 0 M.Qmax)

/-- Profit when selling quantity `Q` at the market-clearing price `P_A(Q)`:
`(P_A(Q) - c) Q`. -/
def profit (M : Market) (Q : ℝ) : ℝ := (M.PA Q - M.c) * Q

/-- `Q` is an optimal quantity Q**: it lies in `[0, Q_max]` and maximizes profit there.
The optimal price is then `P** = P_A(Q)` and the maximum profit `Π** = profit M Q`. -/
def IsOptQty (M : Market) (Q : ℝ) : Prop :=
  Q ∈ Set.Icc 0 M.Qmax ∧ ∀ Q' ∈ Set.Icc 0 M.Qmax, profit M Q' ≤ profit M Q

/-- The linear price `P* = (P_m + c) / 2` (§1.4, p. 4). -/
noncomputable def linPrice (M : Market) : ℝ := (M.Pm + M.c) / 2

/-- Demand at price `p`: the largest quantity in `[0, Q_max]` whose inverse-demand price is
at least `p`, `Q_A(p) = sup {Q ∈ [0, Q_max] : p ≤ P_A(Q)}`. -/
noncomputable def demandAt (M : Market) (p : ℝ) : ℝ :=
  sSup {Q : ℝ | Q ∈ Set.Icc 0 M.Qmax ∧ p ≤ M.PA Q}

/-- Profit of the linear pricing rule: `Π* = (P* - c) Q_A(P*)`. -/
noncomputable def linProfit (M : Market) : ℝ :=
  (linPrice M - M.c) * demandAt M (linPrice M)

/-- Profit at quantity `Q` under a linear inverse demand `P(Q) = P_m - b Q` (eq. (1)):
`(P_m - b Q - c) Q`. -/
def linProfitAt (Pm b c Q : ℝ) : ℝ := (Pm - b * Q - c) * Q

end LinearPriceRule.Concave


