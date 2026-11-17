-- Prove2me | Definitions.Def_InvMarketMaking_LOB_Supplement_ppImbalance
-- name    : InvMarketMaking_LOB_Supplement_ppImbalance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:29:27.545192+00:00
-- url     : https://prove2.me/theorems/e6bcc471-324a-4170-aeff-0753a54278dc
-- title:
--   Trades, reward $r_t$ and imbalance $I_t$ of an arbitrary posted-price process; the valuation-only i.i.d. model
-- statement:
--   Let $(V^{\mathrm{sell}}_t,V^{\mathrm{buy}}_t)_{t\ge1}$ be the valuations of the sellers and buyers and let $(B_t,A_t)_{t\ge1}$ be any process of posted bid–ask pairs. In round $t$ the maker **buys** if $V^{\mathrm{sell}}_t\le B_t$ and **sells** if $V^{\mathrm{buy}}_t\ge A_t$. Its **reward** and its **imbalance** (Definition 3.1) are
--   $$
--   r_t=A_t\,\mathbb I(V^{\mathrm{buy}}_t\ge A_t)-B_t\,\mathbb I(V^{\mathrm{sell}}_t\le B_t),\qquad
--   I_t=\sum_{\tau=1}^t\mathbb I(V^{\mathrm{sell}}_\tau\le B_\tau)-\sum_{\tau=1}^t\mathbb I(V^{\mathrm{buy}}_\tau\ge A_\tau),
--   $$
--   with $I_0=0$. The **valuation-only model** for a law $\mathcal V$ on pairs says that the round pairs $(V^{\mathrm{sell}}_t,V^{\mathrm{buy}}_t)$ are measurable, mutually independent across rounds, and each has law $\mathcal V$; the two coordinates of a round may be arbitrarily correlated.
--
--   These are the quantities of Protocol 1 for algorithms other than Algorithm 4 (whose reward and imbalance the published `lobRound` already defines): the two-bit market maker, the algorithms of the lower bound, and the global-balance wrapper.
--
--   **Formalization Note** The price processes and valuations are indexed by $\mathbb N$; round $t\in[T]$ uses index $t$. The model leaves the field $U$ of the published `Market` structure unconstrained, since none of these algorithms uses Algorithm 4's uniform draws.
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Sec. 3, p. 14; Protocol 1, p. 15; Definition 3.1, p. 16; Sec. 3.3, p. 17

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_IsRoundModel

namespace InvMarketMaking.LOB.Supplement

open MeasureTheory ProbabilityTheory

/-- The valuation-only probability model (Maran, Restelli, Stradi, No-Regret Revenue Maximization in
Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Sec. 3, p. 14): the round
pairs `(V^sell_t, V^buy_t)` are measurable, mutually independent across rounds, and each has law `V`.
The two coordinates of a round may be arbitrarily correlated.

**Formalization Note** The family is indexed by `ℕ`; round `t ∈ [T]` uses index `t`, index `0` and
indices beyond the horizon are unused extra draws. The field `U` of `Market` is not constrained: the
algorithms of Theorems 5.13 and 7.1 make no random draws, and Theorem 6.20 carries its own source of
algorithmic randomness. -/
def IsValuationModel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (V : Measure (ℝ × ℝ))
    (M : Market Ω) : Prop :=
  (∀ t, Measurable (M.Vs t) ∧ Measurable (M.Vb t)) ∧
  iIndepFun (fun t ω => (M.Vs t ω, M.Vb t ω)) P ∧
  ∀ t, HasLaw (fun ω => (M.Vs t ω, M.Vb t ω)) V P

/-- The maker buys in round `t` at the posted bid: `I(V^sell_t ≤ B_t)` (Sec. 3, p. 14; Protocol 1,
p. 15), for an arbitrary bid process `bid`. -/
noncomputable def ppBuy {Ω : Type*} (M : Market Ω) (bid : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  if M.Vs t ω ≤ bid t ω then 1 else 0

/-- The maker sells in round `t` at the posted ask: `I(V^buy_t ≥ A_t)` (Sec. 3, p. 14). -/
noncomputable def ppSell {Ω : Type*} (M : Market Ω) (ask : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  if ask t ω ≤ M.Vb t ω then 1 else 0

/-- The reward `r_t = A_t I(V^buy_t ≥ A_t) − B_t I(V^sell_t ≤ B_t)` of round `t` (Protocol 1, Line 4,
p. 15; Sec. 3.3, p. 17) for arbitrary price processes `bid`, `ask`. -/
noncomputable def ppReward {Ω : Type*} (M : Market Ω) (bid ask : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ask t ω * ppSell M ask t ω - bid t ω * ppBuy M bid t ω

/-- The imbalance `I_t = Σ_{τ=1}^t I(V^sell_τ ≤ B_τ) − Σ_{τ=1}^t I(V^buy_τ ≥ A_τ)` (Definition 3.1,
p. 16) for arbitrary price processes; `I_0 = 0`. -/
noncomputable def ppImbalance {Ω : Type*} (M : Market Ω) (bid ask : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    ℝ :=
  ∑ τ ∈ Finset.Icc 1 t, (ppBuy M bid τ ω - ppSell M ask τ ω)

end InvMarketMaking.LOB.Supplement


