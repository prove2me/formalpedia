-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_tup
-- name    : QAdvFew_PoQOracle_tup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:57.255202+00:00
-- url     : https://prove2.me/theorems/f5e91151-e321-407f-8a28-6a494657706b
-- title:
--   Tuple encoding of bit strings
-- statement:
--   Machines with several inputs, such as a verifier $\mathrm{Ver}^O(x,w)$, read them as one string. The **tuple encoding** of $(u_1,\dots,u_k)$ writes each bit $b$ as the pair $1b$ and closes each component with $00$.
--
--   The encoding is injective on lists, self-delimiting, and has length $2\sum_i |u_i| + 2k$, which is polynomial in the component lengths.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §3.2.3, p. 12 (PDF p. 14)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- Tuple encoding of a list of bit strings as one bit string (Goldin, Lombardi, Morimae,
*Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, §3.2.3, p. 12 (PDF p. 14):
machines with several inputs, such as the verifier `Ver^O(x, w)` of Definition 3.2 and the verifier
`V^O` of Definition 3.8, read them as one string). Each bit `b` is written as the pair `1b` and each
component is closed by the separator `00`.

**Formalization Note** The encoding is injective on lists and self-delimiting, and its length is
`2(|u₁| + ⋯ + |u_k|) + 2k`, polynomial in the component lengths; this is the standard pairing a
Turing machine uses to receive `(x, w)` or `(x, r, m₁, …, m_j)`. -/
def tup (l : List Str) : Str :=
  l.flatMap (fun u => u.flatMap (fun b => [true, b]) ++ [false, false])

end QAdvFew.PoQOracle


