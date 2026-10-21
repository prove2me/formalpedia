-- Prove2me | Definitions.Def_IllinoisBrick_Cartel_Model
-- name    : IllinoisBrick_Cartel_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:14.50018+00:00
-- url     : https://prove2.me/theorems/f3590770-194c-441f-b523-31aa68974064
-- title:
--   §3, Table 1, (1), (3), (6), pp. 7–11 — two manufacturers, two Cournot retailers, five payment schedules, retailer equilibrium, competitive terms, cartel conditions C1–C2
-- statement:
--   This is the deterministic-demand model of Jain, Hasija and Netessine. Two manufacturers $M_1, M_2$ make a homogeneous product at common marginal cost $c$ and sell it to two retailers $R_1, R_2$, who compete in quantities (Cournot) in a consumer market with inverse demand
--   $$p = a - b\,(q_1 + q_2),$$
--   where $q_i$ is the quantity bought (and sold) by retailer $R_i$. The **standing assumptions** are $0 < b$ and $c < a$.
--
--   **Contracts (Table 1).** A manufacturer offers payment terms $v = \{w, \alpha, \xi, f, q_{\min}\}$ of one of five contract structures; $T(v, q, r)$ is the payment of a retailer to its manufacturer for quantity $q$ when the revenue from selling it is $r$:
--
--   1. wholesale price (WP): $T = wq$;
--   2. revenue sharing (RS), $0 \le \alpha \le 1$: $T = wq + \alpha r$;
--   3. quantity discount (QD), $c \le w$, $0 \le \xi$: $T = wq - \xi q^2/2$ if $\xi q \le w - c$, and $T = (w-c)^2/(2\xi) + cq$ otherwise, which is $T(v, \tfrac{w-c}{\xi}, r) + c\,(q - \tfrac{w-c}{\xi})$;
--   4. wholesale price plus fixed fee (WPFF): $T = wq + f\,\mathbb I(q > 0)$, where $f < 0$ is a slotting fee paid to the retailer;
--   5. minimum order quantity (MOQ), $0 \le q_{\min}$: $T = wq$, with purchases restricted to $q \ge q_{\min}$.
--
--   Terms are **admissible** for a contract when the fields the contract does not use are $0$ and the stated ranges hold.
--
--   **Profits.** Retailer $R_i$ buys from manufacturer $M_i$ at terms $v_i$. With revenue $r_i = (a - b(q_1+q_2))\,q_i$, the profits are
--   $$\pi_i = r_i - T(v_i, q_i, r_i), \qquad \Pi_j = T(v_j, q_j, r_j) - c\,q_j .$$
--
--   **Retailer equilibrium.** Given $v = [v_1, v_2]$, a pair $(q_1, q_2)$ is a retailer equilibrium if each $q_i$ is feasible ($q_i \ge 0$, and $q_i \ge q_{\min}$ under MOQ) and maximizes $\pi_i$ over feasible quantities, the rival's quantity held fixed (a pure Nash equilibrium of problem (1)).
--
--   **Competitive terms (Proposition 1).** $v^C$ has $w = c$ and all other terms $0$, except under MOQ, where $q_{\min} = (a-c)/(4b)$.
--
--   **Cartel (problem (6)).** Terms $v$ with retailer equilibrium $q$ satisfy the cartel conditions against a retailer equilibrium $q^C$ under $[v^C, v^C]$ when
--   $$\text{(C1)}\ \ \Pi_j(v, q) > \Pi_j(v^C, q^C)\ \ (j = 1,2), \qquad \text{(C2)}\ \ \pi_i(v, q) \ge \pi_i(v^C, q^C)\ \ (i = 1,2).$$
--
--   These objects are the whole model behind the paper's Propositions 1 and 2.
--
--   **Formalization Note** Demand is deterministic (§4 opening), so the expectations in (1)–(6) disappear and the quantity sold equals the quantity bought (no stage-3 disposal). The paper does not state $0 < b$ or $c < a$; without $c < a$ there is no trade and Proposition 2(b) fails. Retailer $i$ always sources from manufacturer $i$; the paper fixes this for identical terms (p. 9) and the mission adopts it for unequal terms too. The revenue $r$ in the RS payment is the retailer's sales revenue $(a - bQ)q$. The admissible ranges of $\alpha$, $\xi$, $w$ (QD) and $q_{\min}$ are readings of the text ("share of generated revenue", "no unit is sold below the marginal cost"). Proposition 1(e) prints $q_{\min} = q^*$, with $q^*$ the centralized total. The formal statement corrects this to each retailer's half $q^*/2 = (a-c)/(4b)$. The literal per-retailer minimum permits a cartel counterexample to Proposition 2(a), even when the paper's stage-3 option to sell less than purchased is retained; the numerical instance is in MODERATION_NOTES.md. Equilibrium is the published generic pure Nash relation `CarbonDoubleCount.Planner.IsPureNash`; retailers and manufacturers are indexed by `Fin 2` (index `0` is $R_1$/$M_1$).
-- source:
--   Jain, Hasija, Netessine, Supply chains and antitrust governance, accepted manuscript (Management Science 67(11), 2021; LBS Research Online eprint 1493), pp. 7–13 (PDF 8–14), §3, Table 1, (1)–(3), (6), Proposition 1

import Mathlib
import Definitions.Def_CarbonDoubleCount_Planner_PureGame

namespace IllinoisBrick.Cartel

/-- The five contract structures of Table 1 (p. 10): wholesale price (WP), revenue sharing (RS),
quantity discount (QD), wholesale price plus fixed fee (WPFF), minimum order quantity (MOQ). -/
inductive Contract
  | WP
  | RS
  | QD
  | WPFF
  | MOQ
  deriving DecidableEq

/-- A manufacturer's payment terms `v`. Each contract uses only some of the fields
(Table 1: WP `{w}`, RS `{w, α}`, QD `{w, ξ}`, WPFF `{w, f}`, MOQ `{w, q_min}`); `Admissible`
sets the unused fields to `0`. -/
structure Terms where
  /-- per-unit (wholesale) price `w` -/
  w : ℝ
  /-- revenue share `α` (RS) -/
  α : ℝ
  /-- quantity-discount coefficient `ξ` (QD) -/
  ξ : ℝ
  /-- fixed fee `f` paid by the retailer when it buys a positive quantity (WPFF);
  `f < 0` is a slotting fee paid to the retailer -/
  f : ℝ
  /-- minimum order quantity `q_min` (MOQ) -/
  qmin : ℝ

/-- Standing assumptions on the deterministic inverse demand `p = a - b Q` and the common
marginal cost `c`: `0 < b` and `c < a` (added; the paper does not state them). -/
def Standing (a b c : ℝ) : Prop := 0 < b ∧ c < a

/-- Admissible terms of contract type `k`: unused fields are `0`; RS has `0 ≤ α ≤ 1`;
QD has `c ≤ w` and `0 ≤ ξ`; MOQ has `0 ≤ q_min`; WP and WPFF allow any real `w` (and `f`). -/
def Admissible (c : ℝ) : Contract → Terms → Prop
  | .WP, v => v.α = 0 ∧ v.ξ = 0 ∧ v.f = 0 ∧ v.qmin = 0
  | .RS, v => 0 ≤ v.α ∧ v.α ≤ 1 ∧ v.ξ = 0 ∧ v.f = 0 ∧ v.qmin = 0
  | .QD, v => c ≤ v.w ∧ 0 ≤ v.ξ ∧ v.α = 0 ∧ v.f = 0 ∧ v.qmin = 0
  | .WPFF, v => v.α = 0 ∧ v.ξ = 0 ∧ v.qmin = 0
  | .MOQ, v => 0 ≤ v.qmin ∧ v.α = 0 ∧ v.ξ = 0 ∧ v.f = 0

/-- Table 1 (p. 10): the payment `T(v, q, r)` of a retailer to its manufacturer for quantity `q`
when the revenue from selling it is `r`.
* WP: `w q`;  RS: `w q + α r`;
* QD: `w q - ξ q² / 2` if `q ≤ (w - c)/ξ`, otherwise `T(v, (w - c)/ξ, r) + c (q - (w - c)/ξ)`,
  written as `ξ q ≤ w - c` and `(w - c)² / (2 ξ) + c q` (equal for `ξ > 0`; for `ξ = 0`,
  `c ≤ w` and `q ≥ 0` the first branch applies and `T = w q`);
* WPFF: `w q + f 𝕀(q > 0)`;  MOQ: `w q` (the constraint `q ≥ q_min` is in `feasibleSet`). -/
noncomputable def payment (c : ℝ) : Contract → Terms → ℝ → ℝ → ℝ
  | .WP, v, q, _ => v.w * q
  | .RS, v, q, r => v.w * q + v.α * r
  | .QD, v, q, _ =>
      if v.ξ * q ≤ v.w - c then v.w * q - v.ξ * q ^ 2 / 2
      else (v.w - c) ^ 2 / (2 * v.ξ) + c * q
  | .WPFF, v, q, _ => v.w * q + (if 0 < q then v.f else 0)
  | .MOQ, v, q, _ => v.w * q

/-- Retailer `i`'s sales revenue `r_i = (a - b (q₁ + q₂)) q_i` (deterministic demand; the
quantity sold is the quantity purchased). Index `0` is retailer R1, index `1` is R2. -/
def revenue (a b : ℝ) (q : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  (a - b * (q 0 + q 1)) * q i

/-- Retailer `i`'s profit `π_i = r_i - T(v_i, q_i, r_i)`, problem (1) with deterministic demand.
Retailer `i` buys from manufacturer `i` at terms `v i` (paired sourcing, p. 9). -/
noncomputable def retailerProfit (a b c : ℝ) (k : Contract) (v : Fin 2 → Terms)
    (q : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  revenue a b q i - payment c k (v i) (q i) (revenue a b q i)

/-- Manufacturer `j`'s profit (3) under paired sourcing: `Π_j = T(v_j, q_j, r_j) - c q_j`. -/
noncomputable def manufacturerProfit (a b c : ℝ) (k : Contract) (v : Fin 2 → Terms)
    (q : Fin 2 → ℝ) (j : Fin 2) : ℝ :=
  payment c k (v j) (q j) (revenue a b q j) - c * q j

/-- A retailer's feasible purchase quantities: `q ≥ 0`, and `q ≥ q_min` under MOQ. -/
def feasibleSet (k : Contract) (v : Terms) : Set ℝ :=
  {x | 0 ≤ x ∧ (k = Contract.MOQ → v.qmin ≤ x)}

/-- A retailer equilibrium under contract `k` and terms `v = [v₁, v₂]`: a pure Nash equilibrium of
the retailers' simultaneous quantity game (1), each retailer choosing a feasible quantity. -/
def IsRetailerEq (a b c : ℝ) (k : Contract) (v : Fin 2 → Terms) (q : Fin 2 → ℝ) : Prop :=
  CarbonDoubleCount.Planner.IsPureNash (ι := Fin 2) (strategy := fun _ => ℝ)
    (fun i => feasibleSet k (v i)) (fun i q' => retailerProfit a b c k v q' i) q

/-- Proposition 1's competitive terms `v^C`: `w = c` and every other term `0`, except MOQ, where
`q_min = q*/2 = (a - c)/(4b)`, each retailer's half of the centralized quantity
`q* = (a - c)/(2b)` (reading disclosed in the mission). -/
noncomputable def competitiveTerms (a b c : ℝ) : Contract → Terms
  | .MOQ => ⟨c, 0, 0, 0, (a - c) / (4 * b)⟩
  | _ => ⟨c, 0, 0, 0, 0⟩

/-- Conditions (C1) and (C2) of problem (6) (p. 11): against the competitive outcome, i.e. the terms
`v^C` offered by both manufacturers and a retailer equilibrium `qC` under them, the terms `v` with
retailer equilibrium `q` give each manufacturer a strictly higher profit (C1) and each retailer at
least its competitive profit (C2). -/
def IsCartel (a b c : ℝ) (k : Contract) (v : Fin 2 → Terms) (q qC : Fin 2 → ℝ) : Prop :=
  (∀ j, manufacturerProfit a b c k (fun _ => competitiveTerms a b c k) qC j <
      manufacturerProfit a b c k v q j) ∧
  (∀ i, retailerProfit a b c k (fun _ => competitiveTerms a b c k) qC i ≤
      retailerProfit a b c k v q i)

end IllinoisBrick.Cartel


