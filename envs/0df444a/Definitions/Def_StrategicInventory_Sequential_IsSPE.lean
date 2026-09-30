-- Prove2me | Definitions.Def_StrategicInventory_Sequential_IsSPE
-- name    : StrategicInventory_Sequential_IsSPE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T04:43:15.262711+00:00
-- url     : https://prove2.me/theorems/e24a42c1-dfb7-423b-8f95-9bdbc06bfa52
-- title:
--   Subgame perfect equilibrium of the sequential two-period game, §2.1
-- statement:
--   Fix a demand intercept $\alpha$, a holding cost $h$ and a direct selling cost $s$. A strategy profile $\sigma$ of the sequential game of §2.1 is a **subgame perfect equilibrium** when, at every feasible history (on or off the equilibrium path), the player who moves there follows a rule that satisfies two conditions:
--
--   - it chooses a feasible action;
--   - no feasible alternative action, followed by play according to $\sigma$ afterwards, gives that player a strictly higher total profit.
--
--   The feasible actions are:
--
--   1. wholesale prices $w_1, w_2 \ge 0$;
--   2. in period 1, $0 \le q_1 \le Q_1$;
--   3. in period 2, $Q_2 \ge 0$ and $0 \le q_2 \le I + Q_2$, where $I = Q_1 - q_1$;
--   4. the direct selling quantity $q_s \ge 0$.
--
--   A history is feasible when every action in it is feasible. The condition is imposed at each of the five kinds of decision node: the supplier's direct selling, the buyer's period-2 order, the supplier's period-2 price, the buyer's period-1 order, and the supplier's period-1 price. Profits are the total two-period profits $\Pi_b$ and $\Pi_s$.
--
--   This is the equilibrium notion of Proposition 4.1, Proposition 4.2 and Appendix A of the paper, which use the standard notion without defining it.
--
--   **Formalization Note.** The definition is the one-shot-deviation form of subgame perfection. In a game with finitely many stages, the one-shot-deviation form and subgame perfection coincide. Nonnegative wholesale prices and quantities are the paper's implicit action sets (Eq. (1) is stated for $0 \le w$). Negative wholesale prices would make the buyer's order problem unbounded.
-- source:
--   Guan, Gurnani, Geng & Luo, Strategic Inventory and Supplier Encroachment, MSOM 21(3) 2019, pp. 539–540, §2.1; p. 542, Proposition 4.1

import Mathlib
import Definitions.Def_StrategicInventory_Sequential_Game

namespace StrategicInventory.Sequential

/-- `σ` is a subgame perfect equilibrium of the sequential model with demand
intercept `α`, holding cost `h` and direct selling cost `s`.

Action sets: wholesale prices are `≥ 0`; all quantities are `≥ 0`, with
`q1 ≤ Q1` and `q2 ≤ I + Q2` where `I = Q1 - q1`; `qs ≥ 0`.

At every feasible history (on or off the path) the mover's rule picks a feasible
action, and no feasible alternative action, followed by play according to `σ`,
gives the mover a strictly higher total payoff. In this finite-horizon game this
one-shot-deviation condition at every history is subgame perfection. -/
def IsSPE (α h s : ℝ) (σ : Profile) : Prop :=
  -- Period 2, Stage 3: the supplier's direct selling quantity.
  (∀ w1 Q1 q1 w2 Q2 q2 : ℝ, 0 ≤ w1 → 0 ≤ q1 → q1 ≤ Q1 → 0 ≤ w2 →
      0 ≤ Q2 → 0 ≤ q2 → q2 ≤ (Q1 - q1) + Q2 →
      0 ≤ σ.direct w1 Q1 q1 w2 Q2 q2 ∧
      ∀ qs : ℝ, 0 ≤ qs →
        supplierPayoff α s ⟨w1, Q1, q1, w2, Q2, q2, qs⟩ ≤
          supplierPayoff α s (σ.outcomeAtDirect w1 Q1 q1 w2 Q2 q2)) ∧
  -- Period 2, Stage 2: the buyer's order and sales.
  (∀ w1 Q1 q1 w2 : ℝ, 0 ≤ w1 → 0 ≤ q1 → q1 ≤ Q1 → 0 ≤ w2 →
      0 ≤ (σ.period2 w1 Q1 q1 w2).1 ∧ 0 ≤ (σ.period2 w1 Q1 q1 w2).2 ∧
      (σ.period2 w1 Q1 q1 w2).2 ≤ (Q1 - q1) + (σ.period2 w1 Q1 q1 w2).1 ∧
      ∀ Q2 q2 : ℝ, 0 ≤ Q2 → 0 ≤ q2 → q2 ≤ (Q1 - q1) + Q2 →
        buyerPayoff α h (σ.outcomeAtDirect w1 Q1 q1 w2 Q2 q2) ≤
          buyerPayoff α h (σ.outcomeAtOrder2 w1 Q1 q1 w2)) ∧
  -- Period 2, Stage 1: the supplier's wholesale price.
  (∀ w1 Q1 q1 : ℝ, 0 ≤ w1 → 0 ≤ q1 → q1 ≤ Q1 →
      0 ≤ σ.price2 w1 Q1 q1 ∧
      ∀ w2 : ℝ, 0 ≤ w2 →
        supplierPayoff α s (σ.outcomeAtOrder2 w1 Q1 q1 w2) ≤
          supplierPayoff α s (σ.outcomeAtPrice2 w1 Q1 q1)) ∧
  -- Period 1, Stage 2: the buyer's order and sales.
  (∀ w1 : ℝ, 0 ≤ w1 →
      0 ≤ (σ.period1 w1).2 ∧ (σ.period1 w1).2 ≤ (σ.period1 w1).1 ∧
      ∀ Q1 q1 : ℝ, 0 ≤ q1 → q1 ≤ Q1 →
        buyerPayoff α h (σ.outcomeAtPrice2 w1 Q1 q1) ≤
          buyerPayoff α h (σ.outcomeAtOrder1 w1)) ∧
  -- Period 1, Stage 1: the supplier's wholesale price.
  (0 ≤ σ.w1 ∧
      ∀ w1 : ℝ, 0 ≤ w1 →
        supplierPayoff α s (σ.outcomeAtOrder1 w1) ≤ supplierPayoff α s σ.path)

end StrategicInventory.Sequential


