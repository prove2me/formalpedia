-- Prove2me | Definitions.Def_HScattered_Hyperplanes_qPoch
-- name    : HScattered_Hyperplanes_qPoch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:52.301075+00:00
-- url     : https://prove2.me/theorems/6422a252-1f47-4411-9715-0caff3e8f6f2
-- title:
--   q-Pochhammer symbol $(a;q)_k$ (Definition 5.1)
-- statement:
--   For elements $a, q$ of a commutative ring and $k \in \mathbb N$, the **$q$-Pochhammer symbol** is
--   $$(a;q)_k = (1-a)(1-aq)\cdots(1-aq^{k-1}) = \prod_{i=0}^{k-1}(1 - a q^i),$$
--   with $(a;q)_0 = 1$.
--
--   It is the basic building block of the $q$-binomial theorem (Theorem 5.2) and of the evaluations in §5.4.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 19, Definition 5.1

import Mathlib

namespace HScattered.Hyperplanes

/-- Definition 5.1 (arXiv:1906.10590v2, p. 19): the `q`-Pochhammer symbol
`(a; q)_k = (1 − a)(1 − aq)⋯(1 − aq^{k−1})`; it is `1` for `k = 0`. -/
def qPoch {R : Type*} [CommRing R] (a q : R) (k : ℕ) : R :=
  ∏ i ∈ Finset.range k, (1 - a * q ^ i)

end HScattered.Hyperplanes


