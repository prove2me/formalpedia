-- Prove2me | Definitions.Def_FMMM_TSM_tightE
-- name    : FMMM_TSM_tightE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:18:22.708353+00:00
-- url     : https://prove2.me/theorems/6f0db9b9-a950-4acd-a59e-e9a166f8f9f5
-- title:
--   The edge set of the tight family
-- statement:
--   In the tight family (parameter $m \ge 1$, $n = 4m$ ads, $n$ impression types and $n$ arrivals, draws uniform over the types), the edges are:
--
--   1. for each $i$, the six edges of the cycle $u_i - x_i - v_i - y_i - w_i - z_i - u_i$;
--   2. all pairs $(k, x)$ with $k \in K$, $x \in X$ (a complete bipartite graph between $K$ and $X$);
--   3. all pairs $(w, l)$ with $w \in W$, $l \in L$ (a complete bipartite graph between $L$ and $W$).
--
--   On this family the two suggested matchings algorithm achieves ratio no better than $\alpha$, which shows that the analysis is tight.
--
--   **Formalization Note** The encoding of ads and types by $\mathrm{Fin}\,4 \times \mathrm{Fin}\,m$ is that of the 6-cycle flow.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.5, p. 10 (edges (i)–(iii))

import Mathlib
import Definitions.Def_FMMM_TSM_tightFlow

namespace FMMM.TSM

/-- **The edge set of the tight family.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.5, p. 10: "The set A of advertisers consists of the following parts: a set
K of size n/4 and, for i ∈ [1, n/4], advertisers {u_i, v_i, w_i}. The set I of impressions consists
of the following parts: a set L of size n/4 and, for i ∈ [1, n/4], impressions {x_i, y_i, z_i}. …
The edges E are as follows: (i) For i ∈ [1, n/4], the 6-cycle {u_i − x_i − v_i − y_i − w_i − z_i −
u_i}, (ii) a complete bipartite graph between K and X, and (iii) a complete bipartite graph between
L and W."

With the encoding of `tightFlow` (ads `K, U, V, W` = tags `0, 1, 2, 3`; types `L, X, Y, Z` = tags
`0, 1, 2, 3`), `tightE m` is the union of the 6-cycle edges `tightFlow m`, all pairs `(k, x)` with
`k ∈ K`, `x ∈ X`, and all pairs `(w, l)` with `w ∈ W`, `l ∈ L`. Here `n = 4m` is the number of
ads, of types and of arrivals, and draws are uniform over the `4m` types. -/
def tightE (m : ℕ) : Finset ((Fin 4 × Fin m) × (Fin 4 × Fin m)) :=
  tightFlow m ∪ Finset.univ.filter (fun p => (p.1.1 = 0 ∧ p.2.1 = 1) ∨ (p.1.1 = 3 ∧ p.2.1 = 0))

end FMMM.TSM


