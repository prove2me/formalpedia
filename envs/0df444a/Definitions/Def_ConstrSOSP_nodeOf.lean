-- Prove2me | Definitions.Def_ConstrSOSP_nodeOf
-- name    : ConstrSOSP_nodeOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:17.810331+00:00
-- url     : https://prove2.me/theorems/867efb45-528a-4d29-ad7c-e6d30a04233a
-- title:
--   Node of $[2^n]$ named by an $n$-bit string
-- statement:
--   The circuits of LocalOpt and Iter act on $[2^n]=\{1,\dots,2^n\}$. A bit string $b_0b_1\cdots b_{n-1}$ (least significant bit first) names the node
--   $$
--   \mathrm{node}(b)=1+\sum_{i<n} b_i\,2^i .
--   $$
--   Nodes are compared in the integer order. This is the single place where the $1$-based numbering of $[2^n]$ is fixed.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Definitions 4.1–4.2, pp.17–18

import Mathlib

namespace ConstrSOSP

/-- **The node `[2ⁿ] = {1, …, 2ⁿ}` named by an `n`-bit string** (arXiv:2604.02285, 2 Nov 2026,
Definitions 4.1 and 4.2, pp.17–18, where circuits act on `[2^n]`).

The bit list `b₀ b₁ … b_{n−1}` (least significant first) names the node `1 + Σᵢ bᵢ 2ⁱ`. Nodes are
compared in the integer order.

**Formalization Note** This is the one place where the `1`-based numbering of `[2ⁿ]` is fixed;
`nodeBits` is its inverse on `{1, …, 2ⁿ}`. -/
def nodeOf (bits : List Bool) : ℕ :=
  1 + bits.foldr (fun b acc => (if b then 1 else 0) + 2 * acc) 0

end ConstrSOSP


