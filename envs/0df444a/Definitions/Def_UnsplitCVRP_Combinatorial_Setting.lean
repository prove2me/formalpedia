-- Prove2me | Definitions.Def_UnsplitCVRP_Combinatorial_Setting
-- name    : UnsplitCVRP_Combinatorial_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:26:18.287326+00:00
-- url     : https://prove2.me/theorems/d18c8ad1-068e-4f3e-8c35-7d82317b3927
-- title:
--   Definitions 3–5, pp. 4–5 — CVRP demands, routes, client classes and radial sums; §3 Algorithm 1
-- statement:
--   A normalized unsplittable capacitated vehicle-routing instance has a depot $r$, a finite client set $V$, metric costs $c$, capacity $1$, and one demand $d_v\in(0,1]$ per client. A feasible solution partitions all clients into ordered depot-to-depot routes, each carrying demand at most $1$.
--
--   For $\delta\in[0,1/2]$, small clients have $d_v\le\delta$ and big clients have $d_v>\delta$. For any client set $S$, the radial sums are
--   $$
--   \mathcal D(S)=\sum_{v\in S}2d_vc(r,v),\qquad
--   \mathcal D'(S)=\sum_{v\in S}2c(r,v).
--   $$
--   The definitions also give the least TSP route cost on a client set, the least cost of a capacity-feasible consecutive split of a specified tour, and the minimum cost of one- or two-client routes covering the big clients. Algorithm 1 takes the cheaper of a matching-plus-small-tour split and an all-client tour split at $\delta=1/3$.
--
--   **Formalization Note** Nodes are `Fin (n+1)` with depot $0$; routes are lists. The shared `SupplyChainTheory_vrp` module supplies metric, route-cost and solution-cost definitions. Every real infimum used for a valid instance ranges over a nonempty finite family of nonnegative costs: singleton routes provide feasible candidates. The stored cost of Algorithm 1 is the optimum of its two prescribed branches.
-- source:
--   Friggstad, Mousavi, Rahgoshay, Salavatipour, Improved Approximations for CVRP with Unsplittable Demands, arXiv:2111.08138v1, pp. 4–8, Definitions 3–5, Lemma 7, Algorithm 1

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp

namespace UnsplitCVRP.Combinatorial

open SupplyChainTheory

variable {n : ℕ}

/-- Definition 3, p. 4: normalized, positive, unsplittable client demands. -/
def Demands (d : Fin (n + 1) → ℝ) : Prop :=
  ∀ v, v ≠ 0 → 0 < d v ∧ d v ≤ 1

/-- The client set, excluding the depot. -/
def clients (n : ℕ) : Finset (Fin (n + 1)) := Finset.univ.erase 0

/-- Demand carried by an ordered route. -/
def load (d : Fin (n + 1) → ℝ) (L : List (Fin (n + 1))) : ℝ :=
  (L.map d).sum

/-- Definition 3, p. 4: a solution serving exactly `S`. -/
def IsSolutionOn (d : Fin (n + 1) → ℝ) (S : Finset (Fin (n + 1)))
    (R : List (List (Fin (n + 1)))) : Prop :=
  (∀ L ∈ R, L ≠ [] ∧ (0 : Fin (n + 1)) ∉ L ∧ load d L ≤ 1) ∧
    R.flatten.Nodup ∧ ∀ v, v ∈ R.flatten ↔ v ∈ S

/-- Definition 3, p. 4: a solution of the full CVRP instance. -/
def IsSolution (d : Fin (n + 1) → ℝ) (R : List (List (Fin (n + 1)))) : Prop :=
  IsSolutionOn d (clients n) R

/-- Definition 5, p. 4: the small clients of `S`. -/
noncomputable def smallIn (d : Fin (n + 1) → ℝ) (δ : ℝ) (S : Finset (Fin (n + 1))) :
    Finset (Fin (n + 1)) := S.filter (fun v => d v ≤ δ)

/-- Definition 5, p. 4: the big clients of `S`. -/
noncomputable def bigIn (d : Fin (n + 1) → ℝ) (δ : ℝ) (S : Finset (Fin (n + 1))) :
    Finset (Fin (n + 1)) := S.filter (fun v => δ < d v)

/-- The radial sum on `S`; on all clients it is `𝒟` of Lemma 6. -/
def radial (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (d : Fin (n + 1) → ℝ) (S : Finset (Fin (n + 1))) : ℝ :=
  ∑ v ∈ S, 2 * d v * c 0 v

/-- The radial count on `S`; on the big clients it is `𝒟′_big`. -/
def radialCount (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (S : Finset (Fin (n + 1))) : ℝ :=
  ∑ v ∈ S, 2 * c 0 v

/-- A TSP tour through the depot and exactly the clients of `S`. -/
def IsTourOn (S : Finset (Fin (n + 1))) (A : List (Fin (n + 1))) : Prop :=
  A.Nodup ∧ ∀ v, v ∈ A ↔ v ∈ S

/-- The least TSP route cost on `S`. -/
noncomputable def tspOn (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (S : Finset (Fin (n + 1))) : ℝ :=
  sInf {t | ∃ A, IsTourOn S A ∧ t = routeCost c A}

/-- A partition of the given visiting order into nonempty, capacity-feasible consecutive routes. -/
def IsConsecutiveSplit (d : Fin (n + 1) → ℝ) (A : List (Fin (n + 1)))
    (R : List (List (Fin (n + 1)))) : Prop :=
  R.flatten = A ∧ ∀ L ∈ R, L ≠ [] ∧ load d L ≤ 1

/-- The optimal consecutive partition cost computed by the dynamic program on p. 7. -/
noncomputable def bestSplit (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (d : Fin (n + 1) → ℝ) (A : List (Fin (n + 1))) : ℝ :=
  sInf {t | ∃ R, IsConsecutiveSplit d A R ∧ t = solutionCost c R}

/-- Minimum cost matching with loops in `G_aux`, represented by its one- and two-client tours. -/
noncomputable def matchCost (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (d : Fin (n + 1) → ℝ) (B : Finset (Fin (n + 1))) : ℝ :=
  sInf {t | ∃ R, IsSolutionOn d B R ∧
    (∀ L ∈ R, L.length ≤ 2) ∧ t = solutionCost c R}

/-- Prefix demand through the first `i` clients of `A` (zero-based indexing). -/
def prefixLoad (d : Fin (n + 1) → ℝ) (A : List (Fin (n + 1))) (i : ℕ) : ℝ :=
  load d (A.take i)

/-- Equation (2), p. 5: a tiling endpoint lands in client `i`'s demand interval. -/
def IsBad (d : Fin (n + 1) → ℝ) (δ : ℝ) (A : List (Fin (n + 1)))
    (i : ℕ) (θ : ℝ) : Prop :=
  ∃ ℓ : ℕ, prefixLoad d A i < θ + (ℓ : ℝ) * (1 - δ) ∧
    θ + (ℓ : ℝ) * (1 - δ) ≤ prefixLoad d A (i + 1)

/-- Claim 9's closed-endpoint event for four copies of the depot edge. -/
def IsFourCopies (d : Fin (n + 1) → ℝ) (δ : ℝ) (A : List (Fin (n + 1)))
    (i : ℕ) (θ : ℝ) : Prop :=
  ∃ ℓ : ℕ, prefixLoad d A i < θ + (ℓ : ℝ) * (1 - δ) ∧
    θ + (ℓ : ℝ) * (1 - δ) ≤ prefixLoad d A (i + 1) - δ

/-- Added depot-edge cost in the construction of Lemma 7 at a fixed offset. -/
noncomputable def addedCost (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (d : Fin (n + 1) → ℝ) (δ : ℝ) (A : List (Fin (n + 1))) (θ : ℝ) : ℝ := by
  classical
  exact ∑ i ∈ Finset.range A.length,
    ((if IsBad d δ A i θ then 2 * c 0 (A.getD i 0) else 0) +
     (if δ < d (A.getD i 0) ∧ IsFourCopies d δ A i θ
       then 2 * c 0 (A.getD i 0) else 0))

/-- Algorithm 1, p. 8: the cheaper matching-plus-split and all-client split cost. -/
noncomputable def alg1Cost (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (d : Fin (n + 1) → ℝ) (As Aa : List (Fin (n + 1))) : ℝ :=
  min (matchCost c d (bigIn d (1 / 3 : ℝ) (clients n)) + bestSplit c d As)
    (bestSplit c d Aa)

end UnsplitCVRP.Combinatorial


