-- Prove2me | Definitions.Def_CopycatSI_Game
-- name    : CopycatSI_Game
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:46:21.473738+00:00
-- url     : https://prove2.me/theorems/8135bd97-38e4-4d19-b01d-c364d42ebddd
-- title:
--   Commitment and dynamic contracts: strategy profiles and subgame-perfect equilibrium
-- statement:
--   The two contracts of the paper are extensive-form games between the supplier, the retailer and the copycats.
--
--   1. **Commitment contract.** The supplier announces $(w_1,w_2)\ge 0$; the retailer, observing them, chooses $(q_1,q_2,p_1,p_2)\ge 0$; the copycats, observing $p_2$, choose $p_C\ge 0$.
--   2. **Dynamic contract.** The supplier announces $w_1\ge 0$; the retailer chooses $(q_1,p_1)$; the supplier, observing $q_1$ and $p_1$, announces $w_2\ge 0$; the retailer chooses $(q_2,p_2)$; the copycats, observing $p_2$, choose $p_C$.
--
--   A strategy of each player is a function of the history it observes. A profile is a **subgame-perfect equilibrium** if at every history each player's action is feasible and maximizes its own profit ($\pi_S$, $\pi_R$ or $\pi_C$ of the model) given the other players' continuation strategies: the copycats after every $p_2\ge 0$, the retailer after every announced wholesale price (and, in the dynamic contract, after every period-1 decision), and the supplier at the start (and after every $(w_1,q_1,p_1)$). The **outcome** of a profile is the record of its on-path play: $(w_1,w_2,q_1,q_2,I,s_1,s_2,s_C,p_1,p_2,p_C,\pi_S,\pi_R,\pi_C)$.
--
--   These definitions make "the optimal decisions of the supplier, retailer, and copycats" a statement about every subgame-perfect equilibrium.
--
--   **Formalization Note** The retailer moves before the copycats in period 2 (her first-mover advantage, p.7). The copycats observe $p_2$ only, so their strategy is a function of $p_2$. All prices and orders are restricted to be non-negative.
-- source:
--   Jin–Wu–Chen, Managing Competition from Within and Outside: Using Strategic Inventory and Network Externality to Combat Copycats, SSRN 3826955 (version of 2023-05-17), §2, p.7: Commitment Contract steps 1)–3), Dynamic Contract steps 1)–5)

import Mathlib
import Definitions.Def_CopycatSI_Model

namespace CopycatSI

/-- The copycats' strategy is optimal at every history: for every brand price `p₂ ≥ 0` it observes,
its price `c p₂` is non-negative and maximizes `p_C · D_C(p₂, p_C)` over `p_C ≥ 0`.
Jin–Wu–Chen, SSRN 3826955 (version of 2023-05-17), §2, p.7, step 3 of the commitment contract and
step 5 of the dynamic contract ("Copycats observe p₂ and set price p_C").

**Formalization Note** The copycats observe `p₂` only, so their strategy is a function of `p₂`. -/
def CopycatOptimal (β : ℝ) (c : ℝ → ℝ) : Prop :=
  ∀ p2 : ℝ, 0 ≤ p2 →
    0 ≤ c p2 ∧ ∀ pC : ℝ, 0 ≤ pC → pC * demandC β p2 pC ≤ c p2 * demandC β p2 (c p2)

/-- The retailer's decision under the commitment contract: orders `(q₁, q₂)` and prices
`(p₁, p₂)`, chosen together (§2, p.7, step 2). -/
structure CommitDecision where
  q1 : ℝ
  q2 : ℝ
  p1 : ℝ
  p2 : ℝ

/-- Orders and prices are non-negative. -/
def CommitDecision.Feasible (d : CommitDecision) : Prop :=
  0 ≤ d.q1 ∧ 0 ≤ d.q2 ∧ 0 ≤ d.p1 ∧ 0 ≤ d.p2

/-- A strategy profile of the commitment-contract game (§2, p.7):
1. the supplier announces `(w₁, w₂)`;
2. the retailer, observing `(w₁, w₂)`, chooses `(q₁, q₂, p₁, p₂)`;
3. the copycats, observing `p₂`, choose `p_C`. -/
structure CommitProfile where
  wS : ℝ × ℝ
  retailer : ℝ × ℝ → CommitDecision
  copycat : ℝ → ℝ

/-- The play that follows wholesale prices `w` and retailer decision `d`, the copycats answering
`p₂` with their strategy. -/
def CommitProfile.planAt (σ : CommitProfile) (w : ℝ × ℝ) (d : CommitDecision) : Plan :=
  ⟨w.1, w.2, d.q1, d.q2, d.p1, d.p2, σ.copycat d.p2⟩

/-- The on-path play of a commitment-contract profile. -/
def CommitProfile.play (σ : CommitProfile) : Plan := σ.planAt σ.wS (σ.retailer σ.wS)

/-- Subgame-perfect equilibrium of the commitment-contract game with copycat quality `β` and
holding regime `H` (§2, p.7; `γ = 0`). Every player's action is optimal at every history it can
face, given the other players' continuation strategies:
1. the copycats' price is optimal after every `p₂ ≥ 0` (`CopycatOptimal`);
2. after every `(w₁, w₂)` with `w₁, w₂ ≥ 0`, the retailer's decision is feasible and maximizes her
   profit `π_R` over all feasible decisions;
3. the supplier's `(w₁, w₂)` is non-negative and maximizes `π_S = w₁q₁ + w₂q₂` over all
   non-negative wholesale prices.

**Formalization Note** Wholesale prices, orders and retail prices are non-negative. -/
def CommitProfile.IsSPE (β : ℝ) (H : Holding) (σ : CommitProfile) : Prop :=
  CopycatOptimal β σ.copycat ∧
  (∀ w : ℝ × ℝ, 0 ≤ w.1 → 0 ≤ w.2 →
    (σ.retailer w).Feasible ∧
    ∀ d : CommitDecision, d.Feasible →
      (σ.planAt w d).profitR β H ≤ (σ.planAt w (σ.retailer w)).profitR β H) ∧
  (0 ≤ σ.wS.1 ∧ 0 ≤ σ.wS.2 ∧
    ∀ w : ℝ × ℝ, 0 ≤ w.1 → 0 ≤ w.2 →
      (σ.planAt w (σ.retailer w)).profitS ≤ σ.play.profitS)

/-- The on-path outcome record of a commitment-contract profile. -/
noncomputable def CommitProfile.outcome (β : ℝ) (H : Holding) (σ : CommitProfile) : Outcome :=
  σ.play.outcome β H

/-- A period decision of the retailer under the dynamic contract: an order `q` and a price `p`. -/
structure Order where
  q : ℝ
  p : ℝ

/-- Order and price are non-negative. -/
def Order.Feasible (o : Order) : Prop := 0 ≤ o.q ∧ 0 ≤ o.p

/-- A strategy profile of the dynamic-contract game (§2, p.7). Each strategy is a function of the
history its player observes:
1. the supplier announces `w₁` (`w1`);
2. the retailer, observing `w₁`, orders `q₁` and sets `p₁` (`period1 w₁`);
3. the supplier, observing `w₁`, `q₁` and `p₁`, announces `w₂` (`w2 w₁ (q₁, p₁)`);
4. the retailer, observing `w₁`, `(q₁, p₁)` and `w₂`, orders `q₂` and sets `p₂`
   (`period2 w₁ (q₁, p₁) w₂`);
5. the copycats, observing `p₂`, set `p_C` (`copycat p₂`). -/
structure DynProfile where
  w1 : ℝ
  period1 : ℝ → Order
  w2 : ℝ → Order → ℝ
  period2 : ℝ → Order → ℝ → Order
  copycat : ℝ → ℝ

namespace DynProfile

/-- The play with wholesale prices `w₁, w₂` and retailer decisions `o₁, o₂`, the copycats
answering `p₂` with their strategy. -/
def planAt (σ : DynProfile) (w1 : ℝ) (o1 : Order) (w2 : ℝ) (o2 : Order) : Plan :=
  ⟨w1, w2, o1.q, o2.q, o1.p, o2.p, σ.copycat o2.p⟩

/-- The play after the supplier announces `w₂` following `(w₁, o₁)`, everyone afterwards following
`σ`. -/
def afterW2 (σ : DynProfile) (w1 : ℝ) (o1 : Order) (w2 : ℝ) : Plan :=
  σ.planAt w1 o1 w2 (σ.period2 w1 o1 w2)

/-- The play after the retailer's period-1 decision `o₁` following `w₁`, everyone afterwards
following `σ`. -/
def afterO1 (σ : DynProfile) (w1 : ℝ) (o1 : Order) : Plan :=
  σ.afterW2 w1 o1 (σ.w2 w1 o1)

/-- The play after the supplier announces `w₁`, everyone afterwards following `σ`. -/
def afterW1 (σ : DynProfile) (w1 : ℝ) : Plan := σ.afterO1 w1 (σ.period1 w1)

/-- The on-path play. -/
def play (σ : DynProfile) : Plan := σ.afterW1 σ.w1

/-- Subgame-perfect equilibrium of the dynamic-contract game with copycat quality `β` and holding
regime `H` (§2, p.7; `γ = 0`). Every player's action is optimal at every history it can face,
given the other players' continuation strategies:
1. the copycats' price is optimal after every `p₂ ≥ 0` (`CopycatOptimal`);
2. after every `w₁ ≥ 0`, feasible `(q₁, p₁)` and `w₂ ≥ 0`, the retailer's `(q₂, p₂)` is feasible
   and maximizes `π_R` over all feasible `(q₂, p₂)`;
3. after every `w₁ ≥ 0` and feasible `(q₁, p₁)`, the supplier's `w₂` is non-negative and maximizes
   `π_S` over all `w₂ ≥ 0`;
4. after every `w₁ ≥ 0`, the retailer's `(q₁, p₁)` is feasible and maximizes `π_R` over all
   feasible `(q₁, p₁)`;
5. the supplier's `w₁` is non-negative and maximizes `π_S` over all `w₁ ≥ 0`.

**Formalization Note** Wholesale prices, orders and retail prices are non-negative. The supplier
observes `q₁` and `p₁`, hence the inventory `I` (p.7, step 3). -/
def IsSPE (β : ℝ) (H : Holding) (σ : DynProfile) : Prop :=
  CopycatOptimal β σ.copycat ∧
  (∀ w1 : ℝ, 0 ≤ w1 → ∀ o1 : Order, o1.Feasible → ∀ w2 : ℝ, 0 ≤ w2 →
    (σ.period2 w1 o1 w2).Feasible ∧
    ∀ o2 : Order, o2.Feasible →
      (σ.planAt w1 o1 w2 o2).profitR β H ≤ (σ.afterW2 w1 o1 w2).profitR β H) ∧
  (∀ w1 : ℝ, 0 ≤ w1 → ∀ o1 : Order, o1.Feasible →
    0 ≤ σ.w2 w1 o1 ∧
    ∀ w2 : ℝ, 0 ≤ w2 → (σ.afterW2 w1 o1 w2).profitS ≤ (σ.afterO1 w1 o1).profitS) ∧
  (∀ w1 : ℝ, 0 ≤ w1 →
    (σ.period1 w1).Feasible ∧
    ∀ o1 : Order, o1.Feasible → (σ.afterO1 w1 o1).profitR β H ≤ (σ.afterW1 w1).profitR β H) ∧
  (0 ≤ σ.w1 ∧ ∀ w1 : ℝ, 0 ≤ w1 → (σ.afterW1 w1).profitS ≤ σ.play.profitS)

/-- The on-path outcome record of a dynamic-contract profile. -/
noncomputable def outcome (β : ℝ) (H : Holding) (σ : DynProfile) : Outcome :=
  σ.play.outcome β H

end DynProfile

end CopycatSI


