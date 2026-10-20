-- Prove2me | Definitions.Def_ChainCompSI_Backfire_Model
-- name    : ChainCompSI_Backfire_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:15.82022+00:00
-- url     : https://prove2.me/theorems/2bb04946-0ddd-4639-8c2d-6b949b03e36a
-- title:
--   §2 Model, (1), §3 passive beliefs, Table 1 header, pp. 6–9 — two competing chains, strategic inventory carryover, passive-beliefs equilibrium
-- statement:
--   The model of Li, Li and Chen: two competing supply chains $i \in \{1,2\}$, with $j$ denoting the rival chain. Each chain consists of a manufacturer selling through an exclusive retailer. Production costs are zero.
--
--   1. **Demand** (equation (1), p. 7). In period $t \in \{1,2\}$ the demand for product $i$ is
--   $$D_{it} = 1 - p_{it} + \theta\,(p_{jt} - p_{it}),$$
--   where $p_{it}$ is retailer $i$'s retail price and $\theta > 0$ measures the intensity of chain-to-chain competition. Units sold are $D_{it}^+ = \max(D_{it}, 0)$.
--   2. **Timing** (p. 7). Stage 1: manufacturer $i$ sets the wholesale price $w_{i1} \ge 0$. Stage 2: retailer $i$ sets $p_{i1} \ge 0$ and a carryover $I_i \ge 0$, ordering $Q_{i1} = D_{i1}^+ + I_i$, so that $I_i = (Q_{i1} - D_{i1})^+$ units are carried into period 2 at unit holding cost $h$. Stage 3: manufacturer $i$ sets $w_{i2} \ge 0$. Stage 4: retailer $i$ sets $p_{i2} \ge 0$ and orders $Q_{i2} = (D_{i2}^+ - I_i)^+$; unsold units have no value.
--   3. **Payoffs.** Against rival prices $a_1, a_2$, retailer $i$ earns $p_{i1} D_{i1}^+ - w_{i1}(D_{i1}^+ + I_i) - h I_i$ in period 1 and $p_{i2} D_{i2}^+ - w_{i2}(D_{i2}^+ - I_i)^+$ in period 2; manufacturer $i$ earns $w_{i1}(D_{i1}^+ + I_i)$ and $w_{i2}(D_{i2}^+ - I_i)^+$.
--   4. **Strategies** depend on the firm's own chain only, since firms of chain $j$ observe neither $w_{it}$ nor $Q_{it}$ nor $I_i$ (p. 8): $w_{i1}$; a map $w_{i1} \mapsto (p_{i1}, I_i)$; a map from the own history $(w_{i1}, p_{i1}, I_i)$ to $w_{i2}$; and a map from (own history, $w_{i2}$) to $p_{i2}$.
--   5. **Equilibrium** (§3, p. 8): perfect Bayesian equilibrium with *passive beliefs*. At every own history, chain $i$'s firms believe the rival charges its equilibrium-path prices $p_{j1}^*, p_{j2}^*$, and each firm's action is optimal among feasible actions: the retailer's stage-4 price at every own history with $I_i \ge 0$ and every $w_{i2} \ge 0$; the manufacturer's stage-3 price at every own history with $I_i \ge 0$, anticipating its retailer's response; the retailer's stage-2 choice at every $w_{i1} \ge 0$, anticipating its own chain's period-2 play; and the manufacturer's stage-1 price.
--   6. **SI and NI.** In the strategic-inventory game (SI) each chain may carry any $I_i \ge 0$. In the no-inventory benchmark (NI, p. 9) "a manufacturer only delivers whatever its downstream retailer can sell", i.e. $I_i = 0$. The definition allows a separate choice per chain.
--   7. **Outcomes and profits.** The equilibrium-path rows of Table 1 ($w_{i1}, p_{i1}, D_{i1}, I_i, w_{i2}, p_{i2}, D_{i2}$), and the realized profits $\Pi_i$ (manufacturer) and $\pi_i$ (retailer, including the holding cost $h I_i$), evaluated at both chains' equilibrium-path prices.
--
--   This is the object on which Table 1 and Propositions 1–3 of the paper are stated.
--
--   **Formalization Note** Chains are `Fin 2` and the rival of `i` is `1 - i`. Added conventions, all disclosed: prices are restricted to $w, p \ge 0$ (with $w_{i1} < 0$ and $h < -w_{i1}$ the retailer would want unbounded carryover and no equilibrium would exist); demand is truncated at $0$ in sales; the stage-2 order is placed against realized demand ($Q_{i1} = D_{i1}^+ + I_i$ with $I_i$ chosen), which is the reading under which Table 1 is the equilibrium. The page names a PBE with passive beliefs without writing it out; the encoding above (beliefs are the rival's on-path prices at every own history, sequential rationality at every own history) is ours. On-path accessors are `Profile.w1`, `p1`, `inv`, `w2'`, `p2'`, `D1`, `D2`; the profits are `mfrProfit` ($\Pi_i$) and `retProfit` ($\pi_i$).
-- source:
--   Li, Li & Chen, Strategic Inventories under Supply Chain Competition, SSRN 3003887 (author's copy), pp. 6–9: §2 (model, demand (1) p. 7, timing p. 7, information structure p. 8), §3 (passive beliefs p. 8), §3.1 and Table 1 header (NI benchmark) p. 9

import Mathlib

namespace ChainCompSI.Backfire

/-- Demand (1), p. 7: `D = 1 − p + θ (p_rival − p)` for a chain charging `p` against a rival
charging `pRival`. -/
def demand (θ p pRival : ℝ) : ℝ := 1 - p + θ * (pRival - p)

/-- Units sold: demand truncated at `0` (an added convention; it never binds on the
equilibrium path). -/
def sales (θ p pRival : ℝ) : ℝ := max (demand θ p pRival) 0

/-- The rival chain `j = 3 − i`, here `1 − i` on `Fin 2`. -/
def rival (i : Fin 2) : Fin 2 := 1 - i

/-- Chain `i`'s own history at the start of period 2: its first-period wholesale price,
retail price and the carryover inventory `I`. -/
structure Hist where
  /-- first-period wholesale price `w_{i1}` -/
  w1 : ℝ
  /-- first-period retail price `p_{i1}` -/
  p1 : ℝ
  /-- inventory carried into period 2, `I_i` -/
  I : ℝ

/-- A pure strategy profile of the four-stage game, each firm's strategy depending on its own
chain's history only (contracts are unobservable across chains, p. 8):
* stage 1: manufacturer `i` sets `w_{i1}`;
* stage 2: retailer `i` maps its wholesale price `w_{i1}` to a retail price `p_{i1}` and a
  carryover `I_i` (its order is `Q_{i1} = D_{i1}^+ + I_i`);
* stage 3: manufacturer `i` maps its own history to `w_{i2}`;
* stage 4: retailer `i` maps its own history and `w_{i2}` to `p_{i2}`. -/
structure Profile where
  w1 : Fin 2 → ℝ
  stage2 : Fin 2 → ℝ → ℝ × ℝ
  w2 : Fin 2 → Hist → ℝ
  p2 : Fin 2 → Hist → ℝ → ℝ

/-- Retailer's period-1 payoff against a rival price `a1`: revenue on units sold, minus the
wholesale bill on the order `sales + I`, minus the holding cost `h I`. -/
def retP1 (θ h a1 w1 p1 I : ℝ) : ℝ :=
  p1 * sales θ p1 a1 - w1 * (sales θ p1 a1 + I) - h * I

/-- Manufacturer's period-1 payoff: wholesale price times the order `sales + I`
(production cost is zero). -/
def mfrP1 (θ a1 w1 p1 I : ℝ) : ℝ := w1 * (sales θ p1 a1 + I)

/-- Retailer's period-2 payoff against a rival price `a2`, holding `I` units: revenue on units
sold minus the wholesale bill on the replenishment `(sales − I)^+`; unsold units are worthless. -/
def retP2 (θ a2 I w2 p2 : ℝ) : ℝ := p2 * sales θ p2 a2 - w2 * max (sales θ p2 a2 - I) 0

/-- Manufacturer's period-2 payoff: wholesale price times the replenishment order. -/
def mfrP2 (θ a2 I w2 p2 : ℝ) : ℝ := w2 * max (sales θ p2 a2 - I) 0

/-- Feasible carryover: any `I ≥ 0` under strategic inventory (`si = true`), and `I = 0` in the
no-inventory benchmark (`si = false`, p. 9). -/
def InvFeasible (si : Bool) (I : ℝ) : Prop := if si then 0 ≤ I else I = 0

/-- Both chains may carry strategic inventory (the SI game). -/
def SI : Fin 2 → Bool := fun _ => true

/-- Neither chain carries inventory (the NI benchmark). -/
def NI : Fin 2 → Bool := fun _ => false

/-- On-path first-period retail price of chain `i`. -/
def Profile.p1 (E : Profile) (i : Fin 2) : ℝ := (E.stage2 i (E.w1 i)).1

/-- On-path carryover inventory `I_i` of chain `i`. -/
def Profile.inv (E : Profile) (i : Fin 2) : ℝ := (E.stage2 i (E.w1 i)).2

/-- On-path history of chain `i` at the start of period 2. -/
def Profile.hist (E : Profile) (i : Fin 2) : Hist := ⟨E.w1 i, E.p1 i, E.inv i⟩

/-- On-path second-period wholesale price of chain `i`. -/
def Profile.w2' (E : Profile) (i : Fin 2) : ℝ := E.w2 i (E.hist i)

/-- On-path second-period retail price of chain `i`. -/
def Profile.p2' (E : Profile) (i : Fin 2) : ℝ := E.p2 i (E.hist i) (E.w2' i)

/-- Realized first-period demand of chain `i`, at both chains' on-path prices. -/
def Profile.D1 (θ : ℝ) (E : Profile) (i : Fin 2) : ℝ := demand θ (E.p1 i) (E.p1 (rival i))

/-- Realized second-period demand of chain `i`, at both chains' on-path prices. -/
def Profile.D2 (θ : ℝ) (E : Profile) (i : Fin 2) : ℝ := demand θ (E.p2' i) (E.p2' (rival i))

/-- Retailer `i`'s total payoff from choosing `(p, I)` at stage 2 after wholesale price `w1`,
with the rival's prices believed to be `a1, a2` and play continuing by `E` in period 2 at the
resulting own history. -/
def retCont (θ h a1 a2 : ℝ) (E : Profile) (i : Fin 2) (w1 p I : ℝ) : ℝ :=
  retP1 θ h a1 w1 p I +
    retP2 θ a2 I (E.w2 i ⟨w1, p, I⟩) (E.p2 i ⟨w1, p, I⟩ (E.w2 i ⟨w1, p, I⟩))

/-- Manufacturer `i`'s total payoff from setting `w1` at stage 1, with the rival's prices
believed to be `a1, a2` and play continuing by `E` within chain `i`. -/
def mfrCont (θ a1 a2 : ℝ) (E : Profile) (i : Fin 2) (w1 : ℝ) : ℝ :=
  let p := (E.stage2 i w1).1
  let I := (E.stage2 i w1).2
  mfrP1 θ a1 w1 p I +
    mfrP2 θ a2 I (E.w2 i ⟨w1, p, I⟩) (E.p2 i ⟨w1, p, I⟩ (E.w2 i ⟨w1, p, I⟩))

/-- Perfect Bayesian equilibrium with passive beliefs (§3, p. 8) of the game in which chain `i`
may carry inventory iff `si i`. At every own history, chain `i`'s firms believe the rival
charges its on-path prices `a1 = p_{j1}^*`, `a2 = p_{j2}^*`, and act optimally among
feasible actions (`w ≥ 0`, `p ≥ 0`, feasible carryover):
1. stage 4, at every own history with `I ≥ 0` and every `w2 ≥ 0`;
2. stage 3, at every own history with `I ≥ 0`, anticipating its retailer's stage-4 strategy;
3. stage 2, at every `w1 ≥ 0`, anticipating its own chain's period-2 strategies;
4. stage 1. -/
def IsEq (θ h : ℝ) (si : Fin 2 → Bool) (E : Profile) : Prop :=
  (∀ i : Fin 2, ∀ H : Hist, 0 ≤ H.I → ∀ w : ℝ, 0 ≤ w →
      0 ≤ E.p2 i H w ∧
      ∀ q : ℝ, 0 ≤ q →
        retP2 θ (E.p2' (rival i)) H.I w q ≤ retP2 θ (E.p2' (rival i)) H.I w (E.p2 i H w)) ∧
  (∀ i : Fin 2, ∀ H : Hist, 0 ≤ H.I →
      0 ≤ E.w2 i H ∧
      ∀ w : ℝ, 0 ≤ w →
        mfrP2 θ (E.p2' (rival i)) H.I w (E.p2 i H w) ≤
          mfrP2 θ (E.p2' (rival i)) H.I (E.w2 i H) (E.p2 i H (E.w2 i H))) ∧
  (∀ i : Fin 2, ∀ w1 : ℝ, 0 ≤ w1 →
      0 ≤ (E.stage2 i w1).1 ∧ InvFeasible (si i) (E.stage2 i w1).2 ∧
      ∀ p I : ℝ, 0 ≤ p → InvFeasible (si i) I →
        retCont θ h (E.p1 (rival i)) (E.p2' (rival i)) E i w1 p I ≤
          retCont θ h (E.p1 (rival i)) (E.p2' (rival i)) E i w1
            (E.stage2 i w1).1 (E.stage2 i w1).2) ∧
  (∀ i : Fin 2,
      0 ≤ E.w1 i ∧
      ∀ w : ℝ, 0 ≤ w →
        mfrCont θ (E.p1 (rival i)) (E.p2' (rival i)) E i w ≤
          mfrCont θ (E.p1 (rival i)) (E.p2' (rival i)) E i (E.w1 i))

/-- Manufacturer `i`'s realized profit `Π_i`, at both chains' on-path prices:
`w_{i1}(D_{i1}^+ + I_i) + w_{i2}(D_{i2}^+ − I_i)^+`. -/
def mfrProfit (θ : ℝ) (E : Profile) (i : Fin 2) : ℝ :=
  mfrP1 θ (E.p1 (rival i)) (E.w1 i) (E.p1 i) (E.inv i) +
    mfrP2 θ (E.p2' (rival i)) (E.inv i) (E.w2' i) (E.p2' i)

/-- Retailer `i`'s realized profit `π_i`, at both chains' on-path prices, including the holding
cost `h I_i`. -/
def retProfit (θ h : ℝ) (E : Profile) (i : Fin 2) : ℝ :=
  retP1 θ h (E.p1 (rival i)) (E.w1 i) (E.p1 i) (E.inv i) +
    retP2 θ (E.p2' (rival i)) (E.inv i) (E.w2' i) (E.p2' i)

end ChainCompSI.Backfire


