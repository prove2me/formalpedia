-- Prove2me | Definitions.Def_ESRNegotiation_ShortestPath_Model
-- name    : ESRNegotiation_ShortestPath_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:18.833622+00:00
-- url     : https://prove2.me/theorems/b4fa53df-673b-48cf-9924-c03ed9dd0383
-- title:
--   The ESR network, implementation structures, negotiation gains, and shortest path trees
-- statement:
--   The material network has firms $N=\{0,\ldots,n\}$, with retailer $0$. An arc $(i,j)$ records a purchase by downstream firm $i$ from upstream firm $j$. Two firms may negotiate when a directed material path connects them; these pairs form the ESR network $A^{\mathrm{ESR}}$. Firm $i$ has investment cost $c_i$, and full participation creates revenue $R$, leaving surplus $\Pi=R-\sum_i c_i>0$.
--
--   A feasible implementation structure $T$ is a rooted spanning tree of the ESR network. Each supplier has one downstream parent. Its unique route from the retailer is $P_v(T)$. On each ESR arc $(i,j)$ the downstream bargaining power is $\theta_{i,j}$ and the upstream power is $\theta_{j,i}=1-\theta_{i,j}$, giving $\rho_{i,j}=(1-\theta_{i,j})/\theta_{i,j}$. The objective in equation (9) is
--
--   $$
--   \Gamma(T)=\sum_{v\in N\setminus\{0\}}\prod_{a\in P_v(T)}\rho_a.
--   $$
--
--   A payment is indexed by its supplier endpoint. Firm gains include incoming payments, outgoing payments, revenue for the retailer when everyone invests, and the firm's investment cost. A Nash–Nash payment profile makes each arc payment maximize its two firms' weighted Nash product among payment changes that leave both gains nonnegative, holding all other payments fixed. A shortest path tree has, for each supplier, a root route of minimum total arc cost $\log\rho_{i,j}$ among all simple directed ESR routes to that supplier.
--
--   These definitions give a reusable model for the paper's equilibrium and implementation results.
--
--   **Formalization Note** The power interval is restricted to $0<\theta_{i,j}<1$ so division and logarithms have their intended values. A structure is required to reach the retailer, as the paper's description of a rooted tree says, even though display (1) alone does not exclude disconnected cycles. The parent of the retailer is pinned to itself; its payment is ignored. Routes in the shortest path definition are simple, and all payoffs and costs are real numbers.
-- source:
--   Feng, Li, Lu & Shanthikumar, Implementing environmental and social responsibility programs in supply networks through multi-unit bilateral negotiation, accepted manuscript (SSRN 3309518, January 3, 2021; forthcoming in Management Science), pp. 9–20 (PDF 10–21), §3, §4.1, §4.2, displays (1), (4), (5), (9)

import Mathlib

namespace ESRNegotiation.ShortestPath

open Classical

/-- A material-flow network. Firm `0` is the retailer. -/
structure Network (n : ℕ) where
  A : Fin (n + 1) → Fin (n + 1) → Prop
  θ : Fin (n + 1) → Fin (n + 1) → ℝ
  c : Fin (n + 1) → ℝ
  R : ℝ

/-- A negotiation link exists precisely when a nonempty directed material path exists. -/
def esr {n : ℕ} (N : Network n) (i j : Fin (n + 1)) : Prop :=
  Relation.TransGen N.A i j

/-- The upstream party's power relative to the downstream party's. -/
noncomputable def rho {n : ℕ} (N : Network n) (i j : Fin (n + 1)) : ℝ :=
  (1 - N.θ i j) / N.θ i j

/-- Total gain when every firm invests. -/
def PiGain {n : ℕ} (N : Network n) : ℝ :=
  N.R - ∑ i : Fin (n + 1), N.c i

/-- Standing assumptions for the positive-surplus interior-power model. -/
def Standing {n : ℕ} (N : Network n) : Prop :=
  (∀ i j, esr N i j → 0 < N.θ i j ∧ N.θ i j < 1) ∧
  (∀ i j, esr N i j → N.θ j i = 1 - N.θ i j) ∧
  (∀ i, 0 ≤ N.c i) ∧ 0 < PiGain N

/-- A rooted spanning implementation tree, represented by its supplier parent map. -/
def IsStructure {n : ℕ} (N : Network n)
    (par : Fin (n + 1) → Fin (n + 1)) : Prop :=
  par 0 = 0 ∧
  (∀ j, j ≠ 0 → esr N (par j) j) ∧
  (∀ j, ∃ k : ℕ, (par^[k]) j = 0)

/-- The subtype of feasible implementation structures. -/
def Structure {n : ℕ} (N : Network n) :=
  {par : Fin (n + 1) → Fin (n + 1) // IsStructure N par}

/-- Number of parent steps from a supplier to the retailer. -/
noncomputable def depth {n : ℕ} {N : Network n} (T : Structure N)
    (j : Fin (n + 1)) : ℕ :=
  Nat.find (T.property.2.2 j)

/-- The arcs of the unique retailer-to-firm route, listed from the firm toward the root. -/
noncomputable def rootPath {n : ℕ} {N : Network n} (T : Structure N)
    (j : Fin (n + 1)) : List (Fin (n + 1) × Fin (n + 1)) :=
  (List.range (depth T j)).map (fun m => ((T.val^[m + 1]) j, (T.val^[m]) j))

/-- Product of relative bargaining powers along the retailer-to-firm route. -/
noncomputable def pathProd {n : ℕ} (N : Network n) (T : Structure N)
    (v : Fin (n + 1)) : ℝ :=
  ((rootPath T v).map (fun a => rho N a.1 a.2)).prod

/-- Equation (9): sum of the path products for every supplier. -/
noncomputable def Gamma {n : ℕ} (N : Network n) (T : Structure N) : ℝ :=
  ∑ v ∈ (Finset.univ : Finset (Fin (n + 1))).erase 0, pathProd N T v

/-- Firm `j` is on firm `u`'s root route (including `u = j`). -/
noncomputable def inSubtree {n : ℕ} {N : Network n} (T : Structure N)
    (j u : Fin (n + 1)) : Prop :=
  ∃ m < depth T u, (T.val^[m]) u = j

/-- Firm gain at universal participation, given payments indexed by supplier. -/
noncomputable def gain {n : ℕ} (N : Network n) (T : Structure N)
    (w : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).filter
      (fun j => j ≠ 0 ∧ T.val j = i), w j) -
  (if i = 0 then 0 else w i) +
  (if i = 0 then N.R else 0) - N.c i

/-- Firm gain at an arbitrary binary investment profile and contingent payments. -/
noncomputable def gainX {n : ℕ} (N : Network n) (T : Structure N)
    (wx : (Fin (n + 1) → Bool) → Fin (n + 1) → ℝ)
    (x : Fin (n + 1) → Bool) (i : Fin (n + 1)) : ℝ :=
  (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).filter
      (fun j => j ≠ 0 ∧ T.val j = i), wx x j) -
  (if i = 0 then 0 else wx x i) +
  (if i = 0 then N.R * ∏ j : Fin (n + 1), (if x j then (1 : ℝ) else 0) else 0) -
  N.c i * (if x i then 1 else 0)

/-- The two-person weighted Nash product on nonnegative gains. -/
noncomputable def nashProduct (θ a b : ℝ) : ℝ :=
  a ^ θ * b ^ (1 - θ)

/-- Every parent-child payment is a best reply, with other payments held fixed. -/
noncomputable def IsNashNash {n : ℕ} (N : Network n) (T : Structure N)
    (w : Fin (n + 1) → ℝ) : Prop :=
  ∀ j : Fin (n + 1), j ≠ 0 →
    0 ≤ gain N T w (T.val j) ∧ 0 ≤ gain N T w j ∧
    ∀ y : ℝ, let w' := Function.update w j y
      0 ≤ gain N T w' (T.val j) → 0 ≤ gain N T w' j →
      nashProduct (N.θ (T.val j) j)
        (gain N T w' (T.val j)) (gain N T w' j) ≤
      nashProduct (N.θ (T.val j) j)
        (gain N T w (T.val j)) (gain N T w j)

/-- The all-investment payment of Theorem 1. -/
noncomputable def wStar {n : ℕ} (N : Network n) (T : Structure N)
    (j : Fin (n + 1)) : ℝ :=
  ((∑ v ∈ (Finset.univ : Finset (Fin (n + 1))).filter
      (fun v => v ≠ 0 ∧ inSubtree T j v), pathProd N T v) /
      (1 + Gamma N T)) * PiGain N +
  ∑ v ∈ (Finset.univ : Finset (Fin (n + 1))).filter
      (fun v => inSubtree T j v), N.c v

/-- Payments are zero unless every firm invests. -/
noncomputable def contingentWStar {n : ℕ} (N : Network n) (T : Structure N)
    (x : Fin (n + 1) → Bool) (j : Fin (n + 1)) : ℝ :=
  if ∀ i, x i = true then wStar N T j else 0

/-- A simple directed route in the ESR negotiation graph. -/
def IsESRPath {n : ℕ} (N : Network n) (v : Fin (n + 1))
    (l : List (Fin (n + 1))) : Prop :=
  l.head? = some 0 ∧ l.getLast? = some v ∧ l.Chain' (esr N) ∧ l.Nodup

/-- Additive log cost of a route in the negotiation graph. -/
noncomputable def pathCost {n : ℕ} (N : Network n)
    (l : List (Fin (n + 1))) : ℝ :=
  ((l.zip l.tail).map (fun a => Real.log (rho N a.1 a.2))).sum

/-- Additive log cost of a structure's unique root route. -/
noncomputable def rootCost {n : ℕ} (N : Network n) (T : Structure N)
    (v : Fin (n + 1)) : ℝ :=
  ((rootPath T v).map (fun a => Real.log (rho N a.1 a.2))).sum

/-- Every structure route is shortest among all simple ESR routes to its endpoint. -/
noncomputable def IsShortestPathTree {n : ℕ} (N : Network n)
    (T : Structure N) : Prop :=
  ∀ v : Fin (n + 1), v ≠ 0 → ∀ l, IsESRPath N v l →
    rootCost N T v ≤ pathCost N l

end ESRNegotiation.ShortestPath


