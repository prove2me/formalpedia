-- Prove2me | Definitions.Def_ContractUnobs_Compare_Model
-- name    : ContractUnobs_Compare_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:17:18.814482+00:00
-- url     : https://prove2.me/theorems/ca7c66ba-f1ad-4e1d-bf2a-1597de4df998
-- title:
--   §3, §5.1, pp. 7–13 — manufacturer and two price-competing retailers with private contracts: demand, contract classes, conjectured profit, passive-belief equilibrium, realized profits
-- statement:
--   The model of Li and Liu: a monopolist manufacturer, whose unit production cost is normalized to zero, sells one product through two retailers $i \in \{1,2\}$ that compete on price. Retailer $i$'s demand is
--   $$D_i = 1 - p_i + \theta\,(p_j - p_i), \qquad j \ne i,$$
--   where $p_i$ is retailer $i$'s retail price and $\theta \ge 0$ measures the intensity of competition.
--
--   1. **Contracts.** A contract $C = (K, w)$ consists of a fixed fee $K$ and a marginal wholesale price $w$. The *two-part tariff* class is $\{(K,w) : K \in \mathbb R,\ w \ge 0\}$; the *wholesale-price* class is $\{(0,w) : w \ge 0\}$.
--   2. **Actions.** After seeing its own contract, a retailer accepts or rejects, and chooses a price $p \ge 0$ and an order quantity $Q \ge 0$. Units sold are $\min(Q, \max(0, D))$.
--   3. **Conjectured profit.** A retailer that holds the belief $\tilde p$ about its rival's price and accepts $(K,w)$ conjectures the profit
--   $$\tilde\pi = p\,\min\bigl(Q,\ \max(0,\ 1 - p + \theta(\tilde p - p))\bigr) - wQ - K;$$
--   rejecting earns $0$. An action is *optimal* if it maximizes $\tilde\pi$ over all admissible actions and the retailer rejects only when every accepting action has strictly negative conjectured profit.
--   4. **Bilateral profit.** The manufacturer earns $wQ + K$ from a retailer that accepts (it is paid for the quantity ordered) and $0$ from one that rejects.
--   5. **Passive-belief equilibrium.** A profile consists of contracts $C_1^*, C_2^*$ and, for each retailer, a strategy $\sigma_i$ assigning an action to every contract of the class. It is an equilibrium of the game with contract class $\mathcal C$ if (i) $C_1^*, C_2^* \in \mathcal C$; (ii) for every $i$ and every $C \in \mathcal C$, $\sigma_i(C)$ is optimal for the belief $\tilde p_j$ equal to the price in $\sigma_j(C_j^*)$, the rival's equilibrium-path action; (iii) for all $C_1', C_2' \in \mathcal C$,
--   $$\sum_i \text{bilateral}\bigl(C_i', \sigma_i(C_i')\bigr) \le \sum_i \text{bilateral}\bigl(C_i^*, \sigma_i(C_i^*)\bigr).$$
--   6. **Realized profits.** The manufacturer's profit $\Pi$ is the right-hand side above; retailer $i$'s profit $\pi_i$ is $p_i \min(Q_i, \max(0, D_i)) - w_i Q_i - K_i$ evaluated at the actual prices of both retailers on the equilibrium path (and $0$ if it rejects); the industry profit is $\Pi + \pi_1 + \pi_2$.
--
--   Condition (ii) is the passive-beliefs requirement: a retailer receiving an unexpected offer does not revise its belief about the rival's contract, hence about the rival's price. Condition (iii) reflects unobservability: when the manufacturer changes retailer $i$'s contract, retailer $j$ does not see it and keeps its equilibrium action.
--
--   **Formalization Note** Retailers are indexed by `Fin 2`, the rival of `i` is `1 - i`, and all quantities are real. Three conventions are added to the page and needed for an equilibrium to exist and be the paper's: $w \ge 0$ in both contract classes (with $w < 0$ the retailer's order problem is unbounded), $p \ge 0$ (p. 11 implicitly assumes nonnegative demand-inducing prices; without it a rejecting retailer's price can be negative and destroy the rival's conjectured demand), and acceptance when the best conjectured profit is exactly $0$ (as on p. 13, "retailer $j$ will accept"). Demand is truncated at $0$ in sales. A retailer's realized demand uses the rival's price component even if the rival rejects; this does not arise in the equilibria of Propositions 1–2, where both retailers accept.
-- source:
--   Li & Liu, Contract Unobservability and Downstream Competition, SSRN 3339702, pp. 7–8 (§3, demand, contract types, passive beliefs) and p. 13 (§5.1, conjectured profit π̃_i)

import Mathlib

namespace ContractUnobs.Compare

/-- A contract `(K, w)` offered by the manufacturer to one retailer: a fixed fee `K` and a
marginal wholesale price `w` (Li & Liu, §3, p. 8). -/
structure Contract where
  /-- fixed fee -/
  K : ℝ
  /-- marginal wholesale price -/
  w : ℝ

/-- Two-part tariff contracts `(K, w)` with `K ∈ ℝ` and `w ≥ 0` (`w ≥ 0` is an added convention). -/
def tariffClass : Set Contract := {C | 0 ≤ C.w}

/-- Wholesale-price contracts `(0, w)` with `w ≥ 0`. -/
def wholesaleClass : Set Contract := {C | C.K = 0 ∧ 0 ≤ C.w}

/-- A retailer's action after seeing its own contract: accept or reject, a retail price `p`
and an order quantity `Q`. -/
structure Action where
  accept : Bool
  p : ℝ
  Q : ℝ

/-- Admissible actions: a nonnegative price (added convention) and a nonnegative order. -/
def Action.Feasible (a : Action) : Prop := 0 ≤ a.p ∧ 0 ≤ a.Q

/-- Linear demand `D_i = 1 - p_i + θ (p_j - p_i)` (§3, p. 7). -/
def demand (θ p pRival : ℝ) : ℝ := 1 - p + θ * (pRival - p)

/-- Units sold: the order quantity capped by the (nonnegative part of the) demand. -/
def sales (θ p Q pRival : ℝ) : ℝ := min Q (max 0 (demand θ p pRival))

/-- The conjectured profit `π̃_i` of §5.1, p. 13, of a retailer holding the belief `pt` about
the rival's retail price, under contract `C`, when it takes action `a`; rejecting earns `0`. -/
def conjProfit (θ pt : ℝ) (C : Contract) (a : Action) : ℝ :=
  if a.accept then a.p * sales θ a.p a.Q pt - C.w * a.Q - C.K else 0

/-- `a` is an optimal action at contract `C` for the belief `pt`: it is feasible, it maximizes the
conjectured profit over all feasible actions, and it rejects only if every feasible accepting
action has strictly negative conjectured profit (ties are broken towards acceptance). -/
def RetailerOptimal (θ pt : ℝ) (C : Contract) (a : Action) : Prop :=
  a.Feasible ∧ (∀ b : Action, b.Feasible → conjProfit θ pt C b ≤ conjProfit θ pt C a) ∧
  (a.accept = false → ∀ b : Action, b.Feasible → b.accept = true → conjProfit θ pt C b < 0)

/-- What the manufacturer earns from one retailer: `w Q + K` if the retailer accepts
(it is paid for the quantity ordered), `0` otherwise. Production cost is zero. -/
def bilateral (C : Contract) (a : Action) : ℝ := if a.accept then C.w * a.Q + C.K else 0

/-- The other retailer. -/
def rival (i : Fin 2) : Fin 2 := 1 - i

/-- A strategy profile: the two contracts offered, and each retailer's strategy, a map from
every contract it might receive to an action. -/
structure Profile where
  C : Fin 2 → Contract
  σ : Fin 2 → Contract → Action

/-- Retailer `i`'s action on the equilibrium path, at its own equilibrium contract. -/
def Profile.onPath (E : Profile) (i : Fin 2) : Action := E.σ i (E.C i)

/-- Contract equilibrium with passive beliefs for the game in which the manufacturer chooses
contracts from `cls`:
1. both contracts lie in `cls`;
2. at every contract `C ∈ cls`, retailer `i`'s action is optimal for the belief that the rival
   charges its equilibrium-path price (passive beliefs);
3. no pair of contracts in `cls` gives the manufacturer more total profit, each retailer
   reacting to its own contract while its rival keeps its equilibrium-path action. -/
def IsPassiveEq (θ : ℝ) (cls : Set Contract) (E : Profile) : Prop :=
  (∀ i, E.C i ∈ cls) ∧
  (∀ i, ∀ C ∈ cls, RetailerOptimal θ (E.onPath (rival i)).p C (E.σ i C)) ∧
  (∀ C' : Fin 2 → Contract, (∀ i, C' i ∈ cls) →
     ∑ i, bilateral (C' i) (E.σ i (C' i)) ≤ ∑ i, bilateral (E.C i) (E.onPath i))

/-- The manufacturer's realized profit `Π`. -/
def mfrProfit (E : Profile) : ℝ := ∑ i, bilateral (E.C i) (E.onPath i)

/-- Retailer `i`'s realized profit `π_i`, computed with the rival's actual price. -/
def retProfit (θ : ℝ) (E : Profile) (i : Fin 2) : ℝ :=
  let a := E.onPath i
  if a.accept then
    a.p * sales θ a.p a.Q (E.onPath (rival i)).p - (E.C i).w * a.Q - (E.C i).K
  else 0

/-- Total industry profit: the manufacturer's plus both retailers'. -/
def industryProfit (θ : ℝ) (E : Profile) : ℝ := mfrProfit E + ∑ i, retProfit θ E i

end ContractUnobs.Compare


