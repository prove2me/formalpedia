-- Prove2me | Definitions.Def_FlexMargin_longChain
-- name    : FlexMargin_longChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:36:34.832298+00:00
-- url     : https://prove2.me/theorems/2afecb19-4c92-4c83-925c-098a24e6c6bb
-- title:
--   The long chain design $\mathcal L$
-- statement:
--   In a balanced system with $n$ plants and $n$ products, the **long chain** is the design in which plant $i$ produces products $i$ and $i+1$, cyclically:
--
--   $$
--   \mathcal L=\{(a_i,b_i),(a_i,b_{i+1}) : i=1,\dots,n-1\}\cup\{(a_n,b_n),(a_n,b_1)\}.
--   $$
--
--   Each product can be produced by exactly two adjacent plants (for $n\ge3$).
--
--   **Formalization Note** Plants and products are numbered $0,\dots,n-1$ and $i+1$ is taken modulo $n$.
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §2, p. 11

import Mathlib

open Finset

namespace FlexMargin

/-- **The long chain design `ℒ`.**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), §2, p. 11: "In a balanced system, we define the long chain design, where each product can be
produced by exactly two adjacent plants, as L = {(ai,bi),(ai,bi+1)|i = 1,...,n−1} ∪
{(an,bn),(an,b1)}".

With plants and products both `Fin n` (0-based), `longChain n` is the set of arcs
`(i, i)` and `(i, i + 1 mod n)`: plant `i` produces products `i` and `i + 1`, and the last plant
produces the last and the first product.

**Formalization Note.** `finRotate n` is `i ↦ i + 1 mod n`. For `n = 2` the set is all four arcs
and for `n = 1` it is the single arc `(0, 0)`, as the printed formula gives. -/
def longChain (n : ℕ) : Finset (Fin n × Fin n) :=
  univ.image (fun i : Fin n => (i, i)) ∪ univ.image (fun i : Fin n => (i, finRotate n i))

end FlexMargin


