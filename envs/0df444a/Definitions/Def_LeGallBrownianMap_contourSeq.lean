-- Prove2me | Definitions.Def_LeGallBrownianMap_contourSeq
-- name    : LeGallBrownianMap_contourSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:11.99208+00:00
-- url     : https://prove2.me/theorems/4c2f47f0-1d6e-496e-946d-202aa309ee69
-- title:
--   The contour sequence $v_0,\dots,v_{pn}$ of white corners
-- statement:
--   For a $p$-tree $\tau$ with $n$ black vertices, $k=\#\tau-1=pn$, the **contour sequence** of $\tau^\circ$ is $v_i=w_{2i}$, $0\le i\le k$, the white vertices visited at even times of the depth-first sequence (each occurrence is a corner of $v_i$). It is extended periodically: $v_{pn+i}=v_i$.
--
--   **Formalization Note** Indices are reduced modulo $k=\#\tau-1$; since $w_{2k}=w_0$ this agrees with the paper on $0\le i\le k$.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.1, p.9; §2.2, p.10 (periodic extension)

import Mathlib
import Definitions.Def_LeGallBrownianMap_depthFirstAux

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.1, p.9:
"Let τ be a p-tree with n black vertices and let k = #τ − 1 = pn. […] The contour sequence of τ°
is by definition the sequence v_0, ..., v_k defined by v_i = w_{2i} for every i ∈ {0, 1, ..., k}",
and §2.2, p.10: "We extend this sequence periodically by putting v_{pn+i} = v_i".

`contourSeq τ i = v_i`, the `i`-th white corner in the depth-first walk, with the index taken
modulo `k = #τ − 1`.

**Formalization Note.** `w` is `depthFirstAux τ #τ []` (a list of length `2k + 1`), and
`v_i = w_{2 (i mod k)}`. Since `w_{2k} = w_0 = ∅`, this agrees with `v_i` for `0 ≤ i ≤ k` and is
the paper's periodic extension beyond. -/
def contourSeq (τ : Finset (List ℕ+)) (i : ℕ) : List ℕ+ :=
  (depthFirstAux τ τ.card []).getD (2 * (i % (τ.card - 1))) []

end LeGallBrownianMap


