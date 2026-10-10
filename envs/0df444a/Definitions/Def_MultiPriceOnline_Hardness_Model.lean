-- Prove2me | Definitions.Def_MultiPriceOnline_Hardness_Model
-- name    : MultiPriceOnline_Hardness_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:42:39.415115+00:00
-- url     : https://prove2.me/theorems/9e1ceeeb-330e-4786-a56b-a3ae51717d4b
-- title:
--   §2, pp. 11–13 — arrival sequences, the deterministic case, the LP (5), OPT, online algorithms and their revenue
-- statement:
--   Fix a setup with $n$ items, each with starting inventory $k$ and the same price set $r^{(1)} < \dots < r^{(m)}$. An **arrival sequence** $\mathcal A$ consists of a number $T$ of customers and purchase probabilities $p^{(j)}_{t,i}$: customer $t$ buys item $i$ at price $j$ with probability $p^{(j)}_{t,i}$. In the **deterministic case** every $p^{(j)}_{t,i}$ is $0$ or $1$.
--
--   The benchmark $\mathrm{OPT}(\mathcal S, \mathcal A)$ is the optimal value of the linear program (5):
--
--   $$\max \sum_{t=1}^T \sum_{i=1}^n \sum_{j=1}^m p^{(j)}_{t,i} r^{(j)} x^{(j)}_{t,i} \quad \text{s.t.} \quad \sum_{t,j} p^{(j)}_{t,i} x^{(j)}_{t,i} \le k\ \ (i \in [n]), \quad \sum_{i,j} x^{(j)}_{t,i} \le 1\ \ (t \in [T]), \quad x \ge 0.$$
--
--   A **deterministic online algorithm** decides what to offer to customer $t$: nothing, or one item $i$ at one price $j$. It may base this on the purchase probabilities of customers $1, \dots, t$ only. It never sees future customers, and it does not know $T$. Customers arrive in order. The offer of item $i$ at price $j$ sells if item $i$ still has inventory, $1 \le j \le m$ and $p^{(j)}_{t,i} = 1$. A sale earns $r^{(j)}$ and uses one unit of item $i$. The **revenue** $\mathrm{ALG}(\mathcal S, \mathcal A)$ is the total earned over the $T$ customers.
--
--   A randomized online algorithm is a random choice $\omega \mapsto \mathrm{alg}(\omega)$ of a deterministic one, with $\omega$ drawn from a probability space. Its expected revenue is $\int \mathrm{ALG}(\mathrm{alg}(\omega), \mathcal A)\, d\mu(\omega)$.
--
--   **Formalization Note** Items and customers are 0-based (`Fin n`, `Fin T`): the paper's item $i$ is index $i-1$. Prices are 1-based. In the deterministic case the purchase outcomes and the algorithm's own past offers are functions of the rows seen so far, so a rule of the rows of customers $0,\dots,t$ is exactly the paper's information set (p. 11) restricted to deterministic arrivals. The rule may offer any price, including one below the highest acceptable price; such offers are dominated but allowed. `OPT` is the real supremum of the LP's objective values. That set is nonempty ($x = 0$). For purchase probabilities in $[0,1]$ and positive prices it is bounded above by (5b), so the supremum is attained. Randomized algorithms are not built into this file; the theorems quantify over a probability space and a measurable choice of deterministic algorithms.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, pp. 11–13, §2: model, online algorithms, LP (5), deterministic case

import Mathlib

namespace MultiPriceOnline.Hardness

open Finset

/-- An arrival sequence for a setup with `n` items (§2, p. 11): the number `T` of customers and the
purchase probabilities `p t i j` of customer `t` (0-based) for item `i` at price `j` (read at
`j = 1, …, m`). -/
structure Arrival (n : ℕ) where
  T : ℕ
  p : Fin T → Fin n → ℕ → ℝ

/-- The deterministic case (p. 12): every purchase probability is `0` or `1`. -/
def IsDeterministic {n : ℕ} (A : Arrival n) : Prop :=
  ∀ t i j, A.p t i j = 0 ∨ A.p t i j = 1

/-- Objective (5a) of the LP (5) for the setup in which every one of the `n` items has inventory
`k` and the price set `r` with `m` prices: `∑_t ∑_i ∑_{j=1}^m p⁽ʲ⁾_{t,i} r⁽ʲ⁾ x⁽ʲ⁾_{t,i}`. -/
def lpObj {n : ℕ} (m : ℕ) (r : ℕ → ℝ) (A : Arrival n) (x : Fin A.T → Fin n → ℕ → ℝ) : ℝ :=
  ∑ t, ∑ i, ∑ j ∈ Icc 1 m, A.p t i j * r j * x t i j

/-- Feasibility for the LP (5): (5b) `∑_t ∑_{j=1}^m p⁽ʲ⁾_{t,i} x⁽ʲ⁾_{t,i} ≤ k` for every item `i`,
(5c) `∑_i ∑_{j=1}^m x⁽ʲ⁾_{t,i} ≤ 1` for every customer `t`, and (5d) `x ≥ 0`. -/
def LPFeasible {n : ℕ} (k m : ℕ) (A : Arrival n) (x : Fin A.T → Fin n → ℕ → ℝ) : Prop :=
  (∀ i, ∑ t, ∑ j ∈ Icc 1 m, A.p t i j * x t i j ≤ (k : ℝ)) ∧
  (∀ t, ∑ i, ∑ j ∈ Icc 1 m, x t i j ≤ 1) ∧
  (∀ t i j, 0 ≤ x t i j)

/-- `OPT(𝒮, 𝒜)`, the optimal value of the LP (5) (p. 12). The set is nonempty (`x = 0`) and, for
purchase probabilities in `[0, 1]` and positive prices, bounded above by `n · k · max_j r⁽ʲ⁾`
(by (5b)), so this supremum is attained. -/
noncomputable def OPT {n : ℕ} (k m : ℕ) (r : ℕ → ℝ) (A : Arrival n) : ℝ :=
  sSup {v | ∃ x, LPFeasible k m A x ∧ v = lpObj m r A x}

/-- A deterministic online algorithm for a setup with `n` items, in the deterministic case. At
customer `t` (0-based) it sees the purchase-probability rows of customers `0, …, t` (the past and
the present customer, never the future, and not the number `T` of customers) and offers either
nothing (`none`) or an item at a price index (`some (i, j)`). In the deterministic case all past
purchase outcomes, and the algorithm's own past offers, are functions of these rows, so this is
the paper's information set (p. 11). The setup (`n`, `k`, the price set) is fixed before the
algorithm is chosen. -/
def OnlineAlg (n : ℕ) : Type := (t : ℕ) → (Fin (t + 1) → Fin n → ℕ → ℝ) → Option (Fin n × ℕ)

/-- Row `s` of an arrival sequence; the zero row past the last customer. -/
noncomputable def row {n : ℕ} (A : Arrival n) (s : ℕ) : Fin n → ℕ → ℝ :=
  if h : s < A.T then A.p ⟨s, h⟩ else fun _ _ => 0

/-- The rows of customers `0, …, t`: what an online algorithm sees at customer `t`. -/
noncomputable def history {n : ℕ} (A : Arrival n) (t : ℕ) : Fin (t + 1) → Fin n → ℕ → ℝ :=
  fun s => row A s

open Classical in
/-- The sale at customer `t` given current stock: the algorithm's offer `(i, j)` sells iff
`t < T`, item `i` is in stock, `1 ≤ j ≤ m`, and customer `t` buys item `i` at price `j`
(`p t i j = 1`). Any other offer sells nothing. -/
noncomputable def sale {n : ℕ} (m : ℕ) (alg : OnlineAlg n) (A : Arrival n) (stock : Fin n → ℕ)
    (t : ℕ) : Option (Fin n × ℕ) :=
  match alg t (history A t) with
  | some (i, j) =>
      if t < A.T ∧ 0 < stock i ∧ 1 ≤ j ∧ j ≤ m ∧ row A t i j = 1 then some (i, j) else none
  | none => none

/-- Remaining inventory before customer `t`: every item starts with `k` units, and a sale of item
`i` uses one unit. -/
noncomputable def stockAt {n : ℕ} (k m : ℕ) (alg : OnlineAlg n) (A : Arrival n) :
    ℕ → Fin n → ℕ
  | 0 => fun _ => k
  | t + 1 =>
      match sale m alg A (stockAt k m alg A t) t with
      | some (i, _) => Function.update (stockAt k m alg A t) i (stockAt k m alg A t i - 1)
      | none => stockAt k m alg A t

/-- `ALG(𝒮, 𝒜)`: the revenue of the deterministic online algorithm `alg` on the arrival sequence
`A`, for the setup in which each of the `n` items has inventory `k` and price set `r`: a sale at
price `j` earns `r⁽ʲ⁾`. -/
noncomputable def revenue {n : ℕ} (k m : ℕ) (r : ℕ → ℝ) (alg : OnlineAlg n) (A : Arrival n) : ℝ :=
  ∑ t ∈ range A.T,
    match sale m alg A (stockAt k m alg A t) t with
    | some (_, j) => r j
    | none => 0

end MultiPriceOnline.Hardness


