-- Prove2me | Definitions.Def_OverlapRouting_vrpOpt
-- name    : OverlapRouting_vrpOpt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:20.352197+00:00
-- url     : https://prove2.me/theorems/741387bd-3e83-4373-91ff-a36e673ff617
-- title:
--   Euclidean tour length $L^*$ and the split-delivery VRP optimum
-- statement:
--   Points are elements of the plane $\mathbb R^2$ with the Euclidean distance $\|a-b\|_2$. For customer locations $x_1,\dots,x_N$:
--
--   1. The **walk length** of a list of points $p_1,\dots,p_k$ is $\sum_{t<k}\|p_t-p_{t+1}\|_2$.
--   2. The **closed tour length** of an ordering $y_1,\dots,y_n$ is $\sum_{k=1}^{n}\|y_k-y_{k+1}\|_2$ with $y_{n+1}=y_1$, and
--   $$L^*=\min_{\sigma}\ \sum_{k=1}^{N}\big\|x_{\sigma(k)}-x_{\sigma(k+1)}\big\|_2$$
--   is the length of the optimal TSP tour through all customers (the depot is not on the tour), the minimum over all orderings $\sigma$.
--   3. A **trip** is a list of stops (customer, delivered amount); its length is that of the walk from the depot $x_0$ through the stops in order and back to $x_0$.
--   4. For a capacity $Q$ and demands $d_1,\dots,d_N\ge0$, a **split-delivery solution** is a finite list of trips in which every delivered amount is nonnegative, every trip delivers at most $Q$ in total, and the amounts delivered to each customer $i$ over all trips sum to $d_i$. The number of trips is not restricted.
--   5. The **optimal split-delivery VRP distance** $\mathrm{VRP}^*(d)$ is the infimum of the total trip length over all split-delivery solutions.
--
--   These are the deterministic routing objects behind $L^*$ and the reoptimization cost $Z^*$ of the paper.
--
--   **Formalization Note** Points are `EuclideanSpace ℝ (Fin 2)`. Delivered amounts are real numbers (the literal reading of "splittable demand"). For $Q\ge1$ the set of solution lengths is nonempty and bounded below by $0$, so the infimum is genuine.
-- source:
--   Ledvina, Qin, Simchi-Levi & Wei, A New Approach for Vehicle Routing with Stochastic Demand: Combining Route Assignment with Process Flexibility, SSRN 3656374 (PDF of 2022-03-11), https://ssrn.com/abstract=3656374, §2.1, pp.5–6 (customers, depot, distances, splittable demand, trips, capacity Q); pp.11–12 and Table 1, p.6 (L*, Z*)

import Mathlib

namespace OverlapRouting

/-- Points of the plane `ℝ²` (Ledvina, Qin, Simchi-Levi & Wei, *A New Approach for Vehicle Routing
with Stochastic Demand*, SSRN 3656374 (2022), §2.1, p.5: "the location for each customer `i` … is
denoted by `xᵢ ∈ ℝ²`").

**Formalization Note.** `EuclideanSpace ℝ (Fin 2)` carries the Euclidean distance, so
`dist a b = ‖a − b‖₂`. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- Length of the polygonal walk that visits the listed points in order:
`walkLength [p₁, …, pₖ] = ‖p₁ − p₂‖ + ⋯ + ‖pₖ₋₁ − pₖ‖` (`0` for fewer than two points). -/
noncomputable def walkLength : List Point → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: l => dist a b + walkLength (b :: l)

/-- Length of the closed tour `y 0 → y 1 → ⋯ → y (n−1) → y 0` (SSRN 3656374, §4.1, p.13: the tour
`1 → 2 → … → N → 1`). It is `0` for `n ≤ 1`. -/
noncomputable def closedTourLength {n : ℕ} (y : Fin n → Point) : ℝ :=
  ∑ k : Fin n, dist (y k) (y (finRotate n k))

/-- `L*`, "the optimal TSP distance travelling through all customers" (SSRN 3656374, pp.11–12;
Table 1, p.6): the minimum, over all orders of the customers, of the closed tour length. The
depot is not on the tour.

**Formalization Note.** The infimum ranges over the finite nonempty type of permutations, so it is
attained (a minimum). -/
noncomputable def tspOpt {N : ℕ} (x : Fin N → Point) : ℝ :=
  ⨅ σ : Equiv.Perm (Fin N), closedTourLength (x ∘ σ)

/-- Length of one **trip** (SSRN 3656374, p.6: "a vehicle departs from the depot, serves one or
multiple customers, and then returns to the depot"): the walk from the depot `x₀` through the
customers of the stop list `t`, in order, and back to `x₀`. A stop is a pair (customer, amount
delivered). The empty trip has length `0`. -/
noncomputable def tripLength {N : ℕ} (x₀ : Point) (x : Fin N → Point)
    (t : List (Fin N × ℝ)) : ℝ :=
  walkLength (x₀ :: t.map (fun s => x s.1) ++ [x₀])

/-- A **split-delivery solution** for capacity `Q` and demands `dem` (SSRN 3656374, p.6: "the
customer demand is splittable, i.e., a customer's demand may be fulfilled in multiple vehicle
visits"; "Each vehicle has integer capacity `Q`, meaning it can fill a total demand of `Q` in one
trip"; "We do not restrict the number of daily trips"): a finite list of trips in which every
delivered amount is nonnegative, every trip delivers at most `Q` in total, and the amounts delivered
to each customer `i` over all trips sum to `dem i`. -/
def IsSplitDeliverySolution {N : ℕ} (Q : ℕ) (dem : Fin N → ℝ)
    (sol : List (List (Fin N × ℝ))) : Prop :=
  (∀ t ∈ sol, ∀ s ∈ t, 0 ≤ s.2) ∧
  (∀ t ∈ sol, (t.map Prod.snd).sum ≤ (Q : ℝ)) ∧
  ∀ i : Fin N, (sol.map fun t => ((t.filter fun s => s.1 = i).map Prod.snd).sum).sum = dem i

/-- Total travel distance of a list of trips. -/
noncomputable def solutionLength {N : ℕ} (x₀ : Point) (x : Fin N → Point)
    (sol : List (List (Fin N × ℝ))) : ℝ :=
  (sol.map (tripLength x₀ x)).sum

/-- The **optimal split-delivery VRP distance** for one demand realization: the infimum of the
total travel distance over all split-delivery solutions with capacity `Q` that meet the demands
`dem` (the per-day problem whose expectation is `Z*`, "the travel cost of reoptimization", SSRN
3656374, pp.11–12).

**Formalization Note.** Delivered amounts are real numbers (the literal "splittable"). The number
of vehicles plays no role because the number of trips is unrestricted (p.6). For `Q ≥ 1` and
nonnegative demands the set is nonempty (one trip per unit, plus one trip for the fractional rest)
and bounded below by `0`, so the real `sInf` is the genuine infimum. -/
noncomputable def vrpOpt {N : ℕ} (x₀ : Point) (x : Fin N → Point) (Q : ℕ)
    (dem : Fin N → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ sol, IsSplitDeliverySolution Q dem sol ∧ solutionLength x₀ x sol = c}

end OverlapRouting


