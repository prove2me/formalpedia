-- Prove2me | Definitions.Def_SupplyChainTheory_vrp
-- name    : SupplyChainTheory_vrp
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T01:02:33.145237+00:00
-- url     : https://prove2.me/theorems/9b06a6f0-1bf8-439f-81e2-99c42ed6ee67
-- title:
--   The capacitated vehicle routing problem with unit demands of Chapter 11: routes, solutions, the optimal VRP and TSP values and the average depot distance
-- statement:
--   The vehicle routing problem of Chapter 11 of Snyder and Shen in the unit-demand setting of
--   Sect. 11.4.1. Nodes are `Fin (n+1)`: the depot $0$ and the customers $1, \dots, n$, with
--   distances $c_{ij}$ that are symmetric, nonnegative, zero on the diagonal and satisfy the
--   triangle inequality (`VRPMetric`). Every customer has demand $1$ and every vehicle capacity
--   $C$, so a vehicle serves at most $C$ customers.
--
--   `closedLength c L` is the length of the closed walk through the nodes of a list in order;
--   `routeCost c L` is the length of a route, from the depot through the customers of $L$ in order
--   and back. A VRP solution (`IsVRPSolution C R`) is a family of routes, each a nonempty list of
--   at most $C$ customers, together visiting every customer exactly once; `solutionCost c R` is the
--   total length of its routes and `vrpOpt c C` is $z^*$, the least such total. A customer tour
--   (`IsCustomerTour L`) lists all customers once, and `tspOpt c` is $z_T$, the length of the
--   optimal TSP tour through the depot and all customers. `avgDepotDist c` is
--   $\bar c = \frac{1}{n}\sum_{i=1}^n c_{0i}$.
--
--   **Formalization Note** The number of vehicles is unrestricted, as in Sect. 11.4; the book's
--   $z^*$ with a fixed fleet of $K$ vehicles is not modeled. Both optimal values are infima of
--   finite nonempty sets under $n \ge 1$ and $C \ge 1$. The TSP tour through all nodes is a
--   single unconstrained route, so no separate tour model is needed.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, Sect. 11.1.3 pp. 465-466 (the VRP), Sect. 11.4.1 p. 495 (unit demands, z*, zT, c̄)

import Mathlib

namespace SupplyChainTheory

/-! ### The vehicle routing problem with unit demands, Sect. 11.1 and 11.4.1 -/

/-- Symmetric nonnegative distances on the nodes `Fin (n+1)` (depot `0`, customers `1, …, n`)
with `cᵢᵢ = 0` and the triangle inequality. -/
structure VRPMetric {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) : Prop where
  symm : ∀ i j, c i j = c j i
  nonneg : ∀ i j, 0 ≤ c i j
  refl : ∀ i, c i i = 0
  triangle : ∀ i j k, c i j ≤ c i k + c k j

/-- The length of the closed walk through the nodes of a list in order and back to its start. -/
def closedLength {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (L : List (Fin (n + 1))) : ℝ :=
  (List.zipWith c L (L.rotate 1)).sum

/-- The length of a route: from the depot through the customers of `L` in order and back. -/
def routeCost {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (L : List (Fin (n + 1))) : ℝ :=
  closedLength c (0 :: L)

/-- A VRP solution with unit demands and vehicle capacity `C`: a family of routes, each a
nonempty list of at most `C` customers, together covering every customer exactly once. -/
def IsVRPSolution {n : ℕ} (C : ℕ) (R : List (List (Fin (n + 1)))) : Prop :=
  (∀ L ∈ R, L ≠ [] ∧ L.length ≤ C ∧ (0 : Fin (n + 1)) ∉ L)
    ∧ (R.flatMap id).Nodup ∧ ∀ v : Fin (n + 1), v ≠ 0 → v ∈ R.flatMap id

/-- The total length of a VRP solution. -/
def solutionCost {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (R : List (List (Fin (n + 1)))) : ℝ :=
  (R.map (routeCost c)).sum

/-- `z*`, the optimal VRP objective with unit demands and capacity `C`. -/
noncomputable def vrpOpt {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (C : ℕ) : ℝ :=
  sInf {z | ∃ R, IsVRPSolution C R ∧ z = solutionCost c R}

/-- A TSP tour through the depot and all customers, as the list of customers in visiting order. -/
def IsCustomerTour {n : ℕ} (L : List (Fin (n + 1))) : Prop :=
  L.Nodup ∧ (0 : Fin (n + 1)) ∉ L ∧ ∀ v : Fin (n + 1), v ≠ 0 → v ∈ L

/-- `z_T`, the length of the optimal TSP tour through all the nodes. -/
noncomputable def tspOpt {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) : ℝ :=
  sInf {z | ∃ L, IsCustomerTour L ∧ z = routeCost c L}

/-- `c̄ = (1/n) ∑ᵢ c₀ᵢ`, the average distance from the depot to the customers. -/
noncomputable def avgDepotDist {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) : ℝ :=
  (∑ i : Fin (n + 1), c 0 i) / n
end SupplyChainTheory


