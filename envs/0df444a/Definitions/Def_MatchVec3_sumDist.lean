-- Prove2me | Definitions.Def_MatchVec3_sumDist
-- name    : MatchVec3_sumDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:40:53.812194+00:00
-- url     : https://prove2.me/theorems/5714b9e3-d4d5-47ee-ad90-49d3b91312a0
-- title:
--   $S_L^*(U)$: the sum over a uniform $L$-subset
-- statement:
--   For $L\le K$, $S_L^*(U)$ is the random vector $\Sigma_L(A)=\sum_{i\in A}u_i$ for $A$ uniform on the $L$-subsets of $[K]$. This definition is its law.
--
--   The paper compares two estimates of the min-entropy of this vector.
--
--   **Formalization Note** It is a `PMF`, so it requires $L\le K$, the paper's own condition (§6, p.17: "assume $K\ge L$, so $S_L^*(U)$ is well defined").
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), §3, p.10

import Mathlib

namespace MatchVec3

/-- **The random sum `S*_L(U)`** (Aggarwal, Obremski, STOC 2027 submission (manuscript sha256
44199413…), §3, p.10): the law of `Σ_L(A) = ∑_{i ∈ A} u_i` for `A` uniform on the `L`-subsets of `[K]`.

**Formalization Note** It is a `PMF`, so it needs `L ≤ K` (§6, p.17: "assume K ≥ L, so S*_L(U) is well
defined"). -/
noncomputable def sumDist {m n K : ℕ} (U : Fin K → Fin n → ZMod m) (L : ℕ) (h : L ≤ K) :
    PMF (Fin n → ZMod m) :=
  (PMF.uniformOfFinset (Finset.powersetCard L (Finset.univ : Finset (Fin K)))
    (Finset.powersetCard_nonempty.2 (by simpa using h))).map fun A => ∑ i ∈ A, U i

end MatchVec3


