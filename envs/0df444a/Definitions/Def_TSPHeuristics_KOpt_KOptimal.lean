-- Prove2me | Definitions.Def_TSPHeuristics_KOpt_KOptimal
-- name    : TSPHeuristics_KOpt_KOptimal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:54:22.63051+00:00
-- url     : https://prove2.me/theorems/b8ef7ec2-7771-4884-9934-7748fd66ed5f
-- title:
--   k-change and k-optimal tours
-- statement:
--   Following Lin (1965), a **$k$-change** of a tour deletes $k$ of its edges and replaces them by $k$ other edges so that another tour is obtained. A tour is **$k$-optimal** if no $k$-change produces a strictly shorter tour.
--
--   Write $E(\tau)$ for the set of (unordered) edges of a tour $\tau$. A $k$-change of a tour $T$ produces exactly a tour $\sigma$ with $|E(T)\setminus E(\sigma)|=k$, so $T$ is $k$-optimal when
--   $$|E(T)\setminus E(\sigma)|=k\ \Longrightarrow\ L(T)\le L(\sigma)\qquad\text{for every tour }\sigma.$$
--
--   The notion measures local optimality under edge-exchange moves; the mission shows that a tour can be $k$-optimal for all $k\le n/4$ and still be almost twice as long as the optimum.
--
--   **Formalization Note** Two versions are defined: `IsKOptimal d k T` for a tour given as a list $T$ of the $n$ nodes (read cyclically, as insertion runs produce it) and `IsKOptimalTour d k τ` for a tour given as a permutation. Edges are elements of `Sym2 (Fin n)`. The comparison is against every tour at edge difference exactly $k$, not only special moves such as segment reversals; for $n\ge 3$ a tour has $n$ distinct edges, so deleting $k$ and adding $k$ is the same as differing in exactly $k$ edges.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, p. 579, §7, definitions of k-change and k-optimal (after Lin [10])

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel

namespace TSPHeuristics.KOpt

/-- The edge set of the tour `τ 0, τ 1, …, τ (n - 1), τ 0`, as unordered pairs. -/
def tourEdges {n : ℕ} (τ : Equiv.Perm (Fin n)) : Finset (Sym2 (Fin n)) :=
  Finset.univ.image (fun i => s(τ i, τ (finRotate n i)))

/-- The edge set of the closed tour through the list `T` in list order (the last entry is joined
to the first), as unordered pairs. -/
def listEdges {n : ℕ} (T : List (Fin n)) : Finset (Sym2 (Fin n)) :=
  (List.zipWith (fun x y => s(x, y)) T (T.rotate 1)).toFinset

/-- k-optimality (p. 579): "Define a k-change of a tour as the deletion of k edges and their
replacement by k other edges so that another tour is obtained. Define a tour as k-optimal (Lin
[10]) if no k-change produces a better tour." The tour is given as the list `T` (in list order,
closed up). A k-change of `T` produces exactly a tour `τ` whose edge set misses exactly `k` of the
edges of `T`; `T` is k-optimal if no such `τ` is strictly shorter. Every tour at edge difference
`k` is compared, not only special moves such as segment reversals. -/
def IsKOptimal {n : ℕ} (d : Fin n → Fin n → ℝ) (k : ℕ) (T : List (Fin n)) : Prop :=
  ∀ τ : Equiv.Perm (Fin n), (listEdges T \ tourEdges τ).card = k →
    TSPHeuristics.Shared.cycleLength d T ≤ TSPHeuristics.Shared.tourLength d τ

/-- k-optimality (p. 579) of the tour given by the permutation `τ`: no tour `σ` whose edge set
misses exactly `k` of the edges of `τ` is strictly shorter than `τ`. -/
def IsKOptimalTour {n : ℕ} (d : Fin n → Fin n → ℝ) (k : ℕ) (τ : Equiv.Perm (Fin n)) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), (tourEdges τ \ tourEdges σ).card = k →
    TSPHeuristics.Shared.tourLength d τ ≤ TSPHeuristics.Shared.tourLength d σ

end TSPHeuristics.KOpt


