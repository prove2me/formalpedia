-- Prove2me | Definitions.Def_MaxEntOCRS_IsMatchingDist
-- name    : MaxEntOCRS_IsMatchingDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:10.985961+00:00
-- url     : https://prove2.me/theorems/566d14c2-8990-453a-9d06-6802908fcaf0
-- title:
--   Probability distributions on the matchings $\mathcal M(G)$
-- statement:
--   A function $\mu$ on the subsets of the edge set $E$ of a finite loopless multigraph $G$ is a **distribution on the matchings** $\mathcal M(G)$ if $\mu(M) \ge 0$ for all $M$, $\mu(M) = 0$ whenever $M$ is not a matching, and $\sum_M \mu(M) = 1$.
--
--   **Formalization Note** Distributions on $\mathcal M(G)$ are weight functions on all edge sets that vanish off the matchings.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 2, p.4

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph

namespace MaxEntOCRS

/-- `μ` is a probability distribution on the set `M(G)` of matchings of `G` (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §2, p.4).

**Formalization Note** A distribution on matchings is a weight function on all edge sets
`Finset E` that is nonnegative, vanishes off the matchings, and sums to one. -/
def IsMatchingDist {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (μ : Finset E → ℝ) : Prop :=
  (∀ M, 0 ≤ μ M) ∧ (∀ M, ¬ EdmondsMatching65.Polyhedron.IsMatching G M → μ M = 0) ∧ ∑ M, μ M = 1

end MaxEntOCRS


