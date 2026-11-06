-- Prove2me | Definitions.Def_ConstrSOSP_nodeBits
-- name    : ConstrSOSP_nodeBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:24.27766+00:00
-- url     : https://prove2.me/theorems/967581d0-d0fe-4e10-816c-a8273b0db53b
-- title:
--   The $n$-bit string of a node of $[2^n]$
-- statement:
--   For a node $v\in[2^n]=\{1,\dots,2^n\}$, its **bit string** is the list of the $n$ binary digits of $v-1$, least significant first. It inverts the node numbering on $\{1,\dots,2^n\}$.
--
--   **Formalization Note** Only used for $1\le v\le 2^n$, where the natural-number subtraction $v-1$ is exact.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Definitions 4.1–4.2, pp.17–18

import Mathlib

namespace ConstrSOSP

/-- **The `n`-bit string of a node `v ∈ [2ⁿ] = {1, …, 2ⁿ}`** (arXiv:2604.02285, 2 Nov 2026,
Definitions 4.1 and 4.2, pp.17–18): the binary digits of `v − 1`, least significant first, padded
to length `n`. It inverts `nodeOf` on `{1, …, 2ⁿ}`.

**Formalization Note** Only used at `1 ≤ v ≤ 2ⁿ`; the natural-number subtraction `v − 1` is then
exact. -/
def nodeBits (n v : ℕ) : List Bool :=
  List.ofFn (fun i : Fin n => (v - 1).testBit i)

end ConstrSOSP


