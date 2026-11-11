-- Prove2me | Definitions.Def_PriceCapacities_LowerBound_CapacitatedCoreset
-- name    : PriceCapacities_LowerBound_CapacitatedCoreset
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:23:23.593897+00:00
-- url     : https://prove2.me/theorems/bed86fe0-a117-4da3-af8b-4ee93bd85e48
-- title:
--   Capacitated $\varepsilon$-coreset (Definition 2.2)
-- statement:
--   Let $P$ be a finite weighted point set in a metric space $X$ with total weight $n$, $k\ge1$, $z\ge1$ and $\varepsilon\in(0,1)$. A weighted point set $Q$ in $X$ (arbitrary points of $X$, nonnegative weights, finite support) of total weight $\mathbf 1(Q)=n$ is a **capacitated $\varepsilon$-coreset** for $P$ if
--   $$\big|\mathrm{cost}_Q(C,h)-\mathrm{cost}_P(C,h)\big|\le\varepsilon\,\mathrm{cost}_P(C,h)\qquad\text{for every } C\in X^k,\ h\in H,$$
--   where $H$ is the set of nonnegative load vectors summing to $n$. Its **size** is the number of distinct points with positive weight, $|\operatorname{supp}Q|$.
--
--   The coreset may place its points anywhere in $X$; it is not required to be a subset of $P$. Because $Q$ and $P$ have the same total weight, the same loads $H$ are feasible for both.
--
--   **Formalization Note.** `IsCapacitatedCoreset k z ε P Q` is `totalWeight Q = totalWeight P` and the inequality for every `C : Fin k → X` and every `h` with `IsFeasibleLoad (totalWeight P) h`. The range $\varepsilon\in(0,1)$ is not part of the predicate; every theorem states its own range of $\varepsilon$. The size is `size Q`.
-- source:
--   Prabhu, Schwiegelshohn, Shyam, The Price of Capacities for Clustering Coresets, STOC 2027 submission (manuscript sha256 ec35f5ef…), p. 5, Definition 2.2

import Mathlib
import Definitions.Def_PriceCapacities_LowerBound_WeightedSets
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCost

open scoped BigOperators NNReal

namespace PriceCapacities.LowerBound

/-!
# Capacitated ε-coresets (Definition 2.2)

Prabhu, Schwiegelshohn, Shyam, *The Price of Capacities for Clustering Coresets*, STOC 2027
submission (manuscript sha256 ec35f5ef…), p. 5, Definition 2.2.

`IsCapacitatedCoreset k z ε P Q`: the weighted point set `Q` (arbitrary points of `X`,
nonnegative weights, finite support) has the same total weight `n = 1(P)` as `P`, and
`|cost_Q(C, h) − cost_P(C, h)| ≤ ε cost_P(C, h)` for every center tuple `C ∈ X^k` and every load
vector `h ∈ H` (nonnegative, summing to `n`). Its size is `size Q = |supp Q|`, the number of
distinct points with positive weight. The source states the definition for `ε ∈ (0, 1)`; every
statement using it carries that restriction itself.
-/

/-- `Q` is a capacitated `ε`-coreset for `P` (Definition 2.2). -/
def IsCapacitatedCoreset {X : Type*} [PseudoMetricSpace X] (k : ℕ) (z ε : ℝ)
    (P Q : WeightedSet X) : Prop :=
  totalWeight Q = totalWeight P ∧
    ∀ (C : Fin k → X) (h : Fin k → ℝ), IsFeasibleLoad (totalWeight P) h →
      |capCost z Q C h - capCost z P C h| ≤ ε * capCost z P C h

end PriceCapacities.LowerBound


