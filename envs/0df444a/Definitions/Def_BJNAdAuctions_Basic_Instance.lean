-- Prove2me | Definitions.Def_BJNAdAuctions_Basic_Instance
-- name    : BJNAdAuctions_Basic_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T16:22:14.521976+00:00
-- url     : https://prove2.me/theorems/9471bacb-d411-41b0-a256-85c1e78fa7f3
-- title:
--   Online ad-auctions instance and the LP pair of Fig. 2
-- statement:
--   An instance of the **online ad-auctions problem** consists of a finite, nonempty set $I$ of buyers and $m$ products, which arrive one by one in the order $1, \dots, m$. Buyer $i$ has a known budget $B(i) > 0$, and $b(i,j) \ge 0$ is the bid of buyer $i$ on product $j$, revealed when $j$ arrives.
--
--   The fractional offline problem is the **packing LP** of Fig. 2 (which the paper calls the *dual*): a vector $y = (y(i,j))$ is feasible when
--   $$
--   y(i,j) \ge 0, \qquad \sum_{i\in I} y(i,j) \le 1 \ \text{ for every product } j, \qquad \sum_{j=1}^m b(i,j)\,y(i,j) \le B(i) \ \text{ for every buyer } i,
--   $$
--   and its value is $\sum_{j=1}^m \sum_{i\in I} b(i,j)\,y(i,j)$. Here $y(i,j)$ is the fraction of product $j$ allocated to buyer $i$.
--
--   The **covering LP** of Fig. 2 (the paper's *primal*) has a variable $x(i)$ for each buyer and $z(j)$ for each product; $(x,z)$ is feasible when
--   $$
--   b(i,j)\,x(i) + z(j) \ge b(i,j) \ \text{ for every pair } (i,j), \qquad x(i) \ge 0, \qquad z(j) \ge 0,
--   $$
--   and its cost is $\sum_{i\in I} B(i)\,x(i) + \sum_{j=1}^m z(j)$.
--
--   These four notions are the common vocabulary of every statement of the mission: the algorithm's guarantee is measured against feasible solutions of the packing LP, and its analysis builds a feasible solution of the covering LP.
--
--   **Formalization Note** Buyers form a type `I` with `[Fintype I]`; products are `Fin m`, whose order is the arrival order. Bids and budgets are real numbers, with the positivity of budgets and non-negativity of bids stored as fields of the structure. Nonemptiness of `I` is a binder of the theorems that need it.
-- source:
--   Buchbinder, Jain & Naor, Online Primal-Dual Algorithms for Maximizing Ad-Auctions Revenue, ESA 2007, DOI 10.1007/978-3-540-75520-3_24, p. 5-6, Section 2 and Fig. 2

import Mathlib

namespace BJNAdAuctions.Basic

/-- An instance of the online ad-auctions problem (Buchbinder–Jain–Naor, ESA 2007, §2, pp. 5–6).
`I` is the finite set of buyers; the `m` products arrive in the order `0, 1, …, m - 1` of `Fin m`.
Buyer `i` has a known budget `B i > 0`; its bid on product `j` is `b i j ≥ 0`. -/
structure Instance (I : Type*) [Fintype I] (m : ℕ) where
  /-- The budget `B(i)` of buyer `i`. -/
  B : I → ℝ
  /-- The bid `b(i, j)` of buyer `i` on product `j`. -/
  b : I → Fin m → ℝ
  B_pos : ∀ i, 0 < B i
  b_nonneg : ∀ i j, 0 ≤ b i j

variable {I : Type*} [Fintype I] {m : ℕ}

/-- Feasibility for the packing LP of Fig. 2 (the paper's "Dual (Packing)"): `y i j ≥ 0`,
every product is allocated with total fraction at most `1`, and no buyer's allocated bids
exceed its budget. -/
def PackingFeasible (inst : Instance I m) (y : I → Fin m → ℝ) : Prop :=
  (∀ i j, 0 ≤ y i j) ∧
  (∀ j, ∑ i, y i j ≤ 1) ∧
  (∀ i, ∑ j, inst.b i j * y i j ≤ inst.B i)

/-- Objective of the packing LP of Fig. 2: `∑_j ∑_i b(i, j) y(i, j)`. -/
def packingValue (inst : Instance I m) (y : I → Fin m → ℝ) : ℝ :=
  ∑ j, ∑ i, inst.b i j * y i j

/-- Feasibility for the covering LP of Fig. 2 (the paper's "Primal (Covering)"):
`b(i, j) x(i) + z(j) ≥ b(i, j)` for every pair `(i, j)`, and `x, z ≥ 0`. -/
def CoveringFeasible (inst : Instance I m) (x : I → ℝ) (z : Fin m → ℝ) : Prop :=
  (∀ i j, inst.b i j ≤ inst.b i j * x i + z j) ∧
  (∀ i, 0 ≤ x i) ∧
  (∀ j, 0 ≤ z j)

/-- Objective of the covering LP of Fig. 2: `∑_i B(i) x(i) + ∑_j z(j)`. -/
def coveringValue (inst : Instance I m) (x : I → ℝ) (z : Fin m → ℝ) : ℝ :=
  ∑ i, inst.B i * x i + ∑ j, z j

end BJNAdAuctions.Basic


