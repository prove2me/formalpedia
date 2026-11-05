-- Prove2me | Definitions.Def_ReusableMatching_IsFeasibleMatching
-- name    : ReusableMatching_IsFeasibleMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:30:32.580479+00:00
-- url     : https://prove2.me/theorems/18e4c39f-6230-4c07-9612-936cef9ed23c
-- title:
--   Feasible reusable matching
-- statement:
--   Let an OBMRR instance with edge set $E$ and usage duration $d$ be given. A set $M$ of pairs (resource, arrival) is a **feasible reusable matching** if
--
--   1. $M\subseteq E$;
--   2. every arrival occurs in at most one pair of $M$;
--   3. if $(i,j)$ and $(i,j')$ are two pairs of $M$ on the same resource with $j<j'$, then $j+d\le j'$.
--
--   Condition 3 says that a resource matched to arrival $j$ is unavailable at arrivals $j+1,\dots,j+d-1$ and available again at $j+d$. The offline optimum is a maximum over feasible reusable matchings, and the output of Periodic Reranking is a feasible reusable matching.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, §1 Problem Formulation, p.2 (availability: "each resource i is available at time j if and only if it had not been matched at some time j′ ∈ [j − d + 1, j − 1]"; footnote 1)

import Mathlib
import Definitions.Def_ReusableMatching_OBMRRInstance

namespace ReusableMatching

/-- **A feasible reusable matching** of an OBMRR instance (arXiv:2110.07084v2, §1, p.2): a set `M`
of edges in which every arrival is matched at most once ("each online vertex is only matched at
most once", footnote 1, p.2), and a resource matched to arrival `j` is not matched again before
arrival `j + d` ("each resource `i` is available at time `j` if and only if it had not been matched
at some time `j′ ∈ [j − d + 1, j − 1]`", p.2).

**Formalization Note.** `M` is a finite set of pairs `(i, j)`; the three conditions are
`M ⊆ E`, two pairs with the same arrival are equal, and two pairs `(i, j)`, `(i, j′)` on the same
resource with `j < j′` satisfy `j + d ≤ j′`. This is the predicate the offline optimum `OPT`
maximizes over, and the output of Periodic Reranking is checked against the same predicate. -/
def IsFeasibleMatching {V : Type*} {n : ℕ} (I : OBMRRInstance V n)
    (M : Finset (V × Fin n)) : Prop :=
  M ⊆ I.E ∧
  (∀ p ∈ M, ∀ q ∈ M, p.2 = q.2 → p = q) ∧
  (∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p.2 < q.2 → (p.2 : ℕ) + I.d ≤ (q.2 : ℕ))

end ReusableMatching


