-- Prove2me | Definitions.Def_StrategicInventory_Sequential_Game
-- name    : StrategicInventory_Sequential_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T04:38:22.371344+00:00
-- url     : https://prove2.me/theorems/29332f5f-01e4-4bb7-b45b-642ca3f8d1f6
-- title:
--   The sequential two-period supplier–buyer game: outcomes, payoffs, strategy profiles, §2.1
-- statement:
--   This file sets up the **sequential model** of Guan, Gurnani, Geng & Luo (2019), §2.1: one supplier and one buyer interact over two periods. Demand is deterministic, with linear inverse demand $p = \alpha - q$ in each period, where $q$ is the total quantity sold in that period. The buyer pays a per-unit holding cost $h$ on inventory carried into period 2. The supplier pays a per-unit cost $s$ to sell directly to the end market. Production cost, the buyer's selling cost, salvage value and fixed costs are zero.
--
--   The sequence of moves is as follows.
--
--   1. Period 1, Stage 1: the supplier quotes a wholesale price $w_1$.
--   2. Period 1, Stage 2: the buyer orders $Q_1$ and sells $q_1 \le Q_1$. It carries the inventory $I = Q_1 - q_1$ into period 2.
--   3. Period 2, Stage 1: the supplier quotes a wholesale price $w_2$.
--   4. Period 2, Stage 2: the buyer orders $Q_2$ and sells $q_2 \le I + Q_2$.
--   5. Period 2, Stage 3: after observing everything above, the supplier sells $q_s$ through its direct channel. The period-2 price is $p_2 = \alpha - (q_2 + q_s)$.
--
--   An **outcome** is the tuple $(w_1, Q_1, q_1, w_2, Q_2, q_2, q_s)$. The total profits of the buyer and of the supplier are
--
--   $$
--   \Pi_b = (\alpha - q_1) q_1 - w_1 Q_1 - h I + (\alpha - q_2 - q_s) q_2 - w_2 Q_2,
--   \qquad
--   \Pi_s = w_1 Q_1 + w_2 Q_2 + (\alpha - q_2 - q_s - s) q_s .
--   $$
--
--   There is no discounting, and units left unsold at the end of period 2 are worth nothing.
--
--   A **strategy profile** $\sigma$ consists of the supplier's first price $w_1$ and one rule for every later decision node. Each rule may depend on the whole history the mover has observed:
--
--   - the buyer's period-1 rule $w_1 \mapsto (Q_1, q_1)$;
--   - the supplier's period-2 price rule $(w_1, Q_1, q_1) \mapsto w_2$;
--   - the buyer's period-2 rule $(w_1, Q_1, q_1, w_2) \mapsto (Q_2, q_2)$;
--   - the supplier's direct-selling rule $(w_1, Q_1, q_1, w_2, Q_2, q_2) \mapsto q_s$.
--
--   The file also defines the **continuation outcome** reached from any history when play follows $\sigma$ from then on. The **equilibrium path** $\mathrm{path}(\sigma)$ is the outcome that $\sigma$ generates from the start. The **inventory** of an outcome is $I = Q_1 - q_1$.
--
--   These objects are shared by every statement of the mission: the equilibrium notion, the equilibrium paths of Appendix A, and Proposition 4.2.
--
--   **Formalization Note.** The payoffs are not displayed as formulas in the paper. They are the ones the paper's equilibrium tables evaluate: for instance, the Region 8 profits of Table A.4 are these payoffs evaluated on the Region 8 path. The demand intercept $\alpha$, the holding cost $h$ and the direct selling cost $s$ are parameters of the payoff functions. Feasibility of actions is imposed in the equilibrium definition, not here.
-- source:
--   Guan, Gurnani, Geng & Luo, Strategic Inventory and Supplier Encroachment, MSOM 21(3) 2019, pp. 539–540, §2.1 (Sequential Model)

import Mathlib

namespace StrategicInventory.Sequential

/-- A terminal history (outcome) of the sequential two-period game of
Guan, Gurnani, Geng & Luo (MSOM 2019, §2.1): the period-1 wholesale price `w1`,
the buyer's period-1 order `Q1` and sales `q1`, the period-2 wholesale price `w2`,
the buyer's period-2 order `Q2` and sales `q2`, and the supplier's direct
selling quantity `qs`. -/
structure Outcome where
  w1 : ℝ
  Q1 : ℝ
  q1 : ℝ
  w2 : ℝ
  Q2 : ℝ
  q2 : ℝ
  qs : ℝ

/-- The buyer's strategic inventory carried into period 2, `I = Q1 - q1`. -/
def Outcome.inventory (o : Outcome) : ℝ := o.Q1 - o.q1

/-- The buyer's total two-period profit, with inverse demand `p = α - q` in each
period, per-unit holding cost `h` on the inventory `I = Q1 - q1`, and zero
selling cost, salvage value and fixed costs:
`(α - q1) q1 - w1 Q1 - h I + (α - q2 - qs) q2 - w2 Q2`. -/
def buyerPayoff (α h : ℝ) (o : Outcome) : ℝ :=
  (α - o.q1) * o.q1 - o.w1 * o.Q1 - h * (o.Q1 - o.q1)
    + (α - o.q2 - o.qs) * o.q2 - o.w2 * o.Q2

/-- The supplier's total two-period profit, with zero production cost and
per-unit direct selling cost `s`: `w1 Q1 + w2 Q2 + (α - q2 - qs - s) qs`. -/
def supplierPayoff (α s : ℝ) (o : Outcome) : ℝ :=
  o.w1 * o.Q1 + o.w2 * o.Q2 + (α - o.q2 - o.qs - s) * o.qs

/-- A pure strategy profile of the sequential game. Every rule may depend on the
full history observed by the mover:
* `w1` — the supplier's period-1 wholesale price;
* `period1 w1 = (Q1, q1)` — the buyer's period-1 order and sales;
* `price2 w1 Q1 q1 = w2` — the supplier's period-2 wholesale price;
* `period2 w1 Q1 q1 w2 = (Q2, q2)` — the buyer's period-2 order and sales;
* `direct w1 Q1 q1 w2 Q2 q2 = qs` — the supplier's direct selling quantity. -/
structure Profile where
  w1 : ℝ
  period1 : ℝ → ℝ × ℝ
  price2 : ℝ → ℝ → ℝ → ℝ
  period2 : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ
  direct : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ

/-- The outcome once the history `(w1, Q1, q1, w2, Q2, q2)` has occurred and the
supplier then follows `σ.direct`. -/
def Profile.outcomeAtDirect (σ : Profile) (w1 Q1 q1 w2 Q2 q2 : ℝ) : Outcome :=
  ⟨w1, Q1, q1, w2, Q2, q2, σ.direct w1 Q1 q1 w2 Q2 q2⟩

/-- The outcome once the history `(w1, Q1, q1, w2)` has occurred and play then
follows `σ` (buyer's period-2 rule, then supplier's direct selling rule). -/
def Profile.outcomeAtOrder2 (σ : Profile) (w1 Q1 q1 w2 : ℝ) : Outcome :=
  σ.outcomeAtDirect w1 Q1 q1 w2 (σ.period2 w1 Q1 q1 w2).1 (σ.period2 w1 Q1 q1 w2).2

/-- The outcome once the history `(w1, Q1, q1)` has occurred and play then
follows `σ` from the supplier's period-2 pricing on. -/
def Profile.outcomeAtPrice2 (σ : Profile) (w1 Q1 q1 : ℝ) : Outcome :=
  σ.outcomeAtOrder2 w1 Q1 q1 (σ.price2 w1 Q1 q1)

/-- The outcome once the supplier has quoted `w1` and play then follows `σ`. -/
def Profile.outcomeAtOrder1 (σ : Profile) (w1 : ℝ) : Outcome :=
  σ.outcomeAtPrice2 w1 (σ.period1 w1).1 (σ.period1 w1).2

/-- The equilibrium path: the outcome generated by the profile `σ`. -/
def Profile.path (σ : Profile) : Outcome :=
  σ.outcomeAtOrder1 σ.w1

end StrategicInventory.Sequential


