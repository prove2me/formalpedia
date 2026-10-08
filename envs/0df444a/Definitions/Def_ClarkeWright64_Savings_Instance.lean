-- Prove2me | Definitions.Def_ClarkeWright64_Savings_Instance
-- name    : ClarkeWright64_Savings_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:24:49.253134+00:00
-- url     : https://prove2.me/theorems/8b7561d6-d91f-4036-b1a4-ae4ed892ae2e
-- title:
--   Formulation, pp. 568–569 — depot, customers, distances, loads, a fleet of truck classes; savings, run loads, mileage, the Table II test
-- statement:
--   A depot $P_0$ serves customers $P_1,\dots,P_M$. Between every two points $P_y, P_z$ the length $d_{y,z}$ of the shortest route is given, and customer $P_j$ requires a load $q_j$. A fleet of trucks comes in $n$ capacity classes: $x_i$ trucks of capacity $C_i$ are available ($i=1,\dots,n$). The problem (p. 568) is to allocate the loads to trucks so that all the merchandise is assigned and the total distance covered is a minimum.
--
--   A **run** is the ordered list of customers $P_{a_1},\dots,P_{a_k}$ that one truck visits; the truck drives $P_0P_{a_1}\cdots P_{a_k}P_0$. This module defines:
--
--   1. the **saving** of the cell $(y:z)$ of the half matrix (p. 573),
--   $$
--   s_{y,z}=d_{0,y}+d_{0,z}-d_{y,z};
--   $$
--   2. the **load** of a run, $\sum_{i=1}^k q_{a_i}$;
--   3. the **mileage** of a family of runs, the sum of the lengths $d_{0,a_1}+d_{a_1,a_2}+\dots+d_{a_{k-1},a_k}+d_{a_k,0}$ of its runs;
--   4. **fleet feasibility** of a multiset of run loads: each run can be given a truck of some class $i$ whose capacity $C_i$ is at least its load, with no class used more than $x_i$ times;
--   5. the **Table II test** (p. 573) on a multiset of run loads: for every capacity level $C_i$,
--   $$
--   \#\{\text{runs with load} > C_i\}\;\le\;\sum_{k>i} x_k ,
--   $$
--   the number of runs in column "Over $C_i$" of Table II does not exceed the number of trucks of capacity greater than $C_i$.
--
--   These are the objects on which the savings procedure and all statements of this mission are built.
--
--   **Formalization Note** Points are `Fin (M+1)` with depot `0`, the convention of the referenced module `SupplyChainTheory_vrp`, whose `routeCost` gives a run's length. Class `i : Fin (n+1)` is the paper's $C_{i+1}$, so the paper's largest capacity $C_n$ is `C (Fin.last n)` and there is always at least one class. Availabilities are in `ℕ∞` because the paper makes $x_1$ infinite. The paper's standing assumptions (symmetric $d$, $C_1<\dots<C_n$, $x_1=\infty$) are hypotheses of the theorems that need them, not part of the structure. Table II is read cumulatively: the printed "Available 7" in column "Over 4000" is $3+4$ trucks of 5000 and 6000 gallons; the column "Up to $C_1$" is not tested because $x_1=\infty$.
-- source:
--   Clarke & Wright, Scheduling of vehicles from a central depot to a number of delivery points, Oper. Res. 12 (1964), pp. 568–569, Formulation; p. 573, Computational procedure (cell values, Table II)

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp

namespace ClarkeWright64.Savings

/-- Clarke & Wright (1964), Formulation, pp. 568–569. A depot `P₀ = 0` and customers
`P₁, …, P_M` (the nonzero elements of `Fin (M+1)`), the distances `d y z`, the loads `q j`
(only the values at customers are used), and a fleet of `n + 1` truck classes: class `i` has
capacity `C i` and `x i` trucks are available. Class `i` is the paper's `C_{i+1}`, so the
paper's largest capacity `C_n` is `C (Fin.last n)`. Availabilities live in `ℕ∞` because the
paper makes `x₁` infinite. The paper's standing assumptions (symmetric `d`, `C₁ < ⋯ < C_n`,
`x₁ = ∞`) are hypotheses of the theorems, not fields. -/
structure Instance (M n : ℕ) where
  d : Fin (M + 1) → Fin (M + 1) → ℝ
  q : Fin (M + 1) → ℝ
  C : Fin (n + 1) → ℝ
  x : Fin (n + 1) → ℕ∞

variable {M n : ℕ}

/-- The cell value of the half matrix, p. 573: the saving `d_{0,y} + d_{0,z} − d_{y,z}` of cell
`(y:z)`. -/
def Instance.saving (I : Instance M n) (y z : Fin (M + 1)) : ℝ :=
  I.d 0 y + I.d 0 z - I.d y z

/-- The load of a run (the ordered list of customers a truck visits): `∑ q_j` over its
customers. -/
def Instance.runLoad (I : Instance M n) (r : List (Fin (M + 1))) : ℝ :=
  (r.map I.q).sum

/-- The total mileage of a family of runs: each run `[a₁, …, a_k]` is driven as the closed
route `P₀ P_{a₁} ⋯ P_{a_k} P₀`, of length `SupplyChainTheory.routeCost d [a₁, …, a_k]`. -/
def Instance.mileage (I : Instance M n) (runs : List (List (Fin (M + 1)))) : ℝ :=
  (runs.map (SupplyChainTheory.routeCost I.d)).sum

/-- "Allocate loads to trucks" (p. 568): every run load in the multiset is carried by a truck of
some class whose capacity it does not exceed, and no class is used more often than it has trucks
available. The pairing `κ` lists each load together with the class of its truck. -/
def Instance.FleetFeasible (I : Instance M n) (loads : Multiset ℝ) : Prop :=
  ∃ κ : Multiset (ℝ × Fin (n + 1)),
    κ.map Prod.fst = loads ∧ (∀ p ∈ κ, p.1 ≤ I.C p.2) ∧
      ∀ i : Fin (n + 1), ((κ.filter (fun p => p.2 = i)).card : ℕ∞) ≤ I.x i

/-- The Table II test, p. 573 (Tables II, IV, VI). For every capacity level `C_i`, the number
of runs whose load exceeds `C_i` (the "Allocated" entry of column "Over C_i") is at most the number
of trucks of capacity greater than `C_i`, i.e. of the classes `k > i` (the "Available" entry). The
column "Up to C₁" is not tested. -/
def Instance.TableIIOK (I : Instance M n) (loads : Multiset ℝ) : Prop :=
  ∀ i : Fin (n + 1),
    (((loads.filter (fun l => I.C i < l)).card : ℕ) : ℕ∞) ≤ ∑ k ∈ Finset.Ioi i, I.x k

end ClarkeWright64.Savings


