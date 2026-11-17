-- Prove2me | Definitions.Def_GyoriLovasz_Supplement_encWInstance
-- name    : GyoriLovasz_Supplement_encWInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:10:50.266626+00:00
-- url     : https://prove2.me/theorems/8a482870-caae-4ec5-9ba0-fb56b5c79e3f
-- title:
--   Binary encoding of a weighted input
-- statement:
--   The weighted input is written on a Turing-machine tape as: the number of weights, the weights one after another, and then the encoding of the unweighted input used for Theorem 1 (the number of vertices, the number of edges, the edges, and the terminal–capacity pairs). Every number is written in **binary** followed by a separator symbol.
--
--   The paper states (p.13) that "the integral weights are given in binary and may be exponentially large", so polynomial time means polynomial in this bit length, not in the values of the weights.
--
--   **Formalization Note** The weight block comes first and is length-prefixed, which makes the encoding injective (proved in the mission's verification file); appending the weights after the unweighted encoding would not be injective.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Theorems 3 and 4, pp.11–12 (polynomial time); p.13 (weights in binary)

import Mathlib
import Definitions.Def_GyoriLovasz_encInstance
import Definitions.Def_GyoriLovasz_Supplement_WInstance

namespace GyoriLovasz

namespace Supplement

open OnlineCRS.Combine

/-- **The input encoding of the weighted algorithm.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the
Exponential Barrier*, arXiv:2608.30945 (held file sha256 3f80f82d…780e), Theorems 3 and 4, pp.11–12
("polynomial-time"), p.13 ("the integral weights are given in binary and may be exponentially large"): the number of
weights, each weight, then the published encoding `encInstance` of the unweighted input, all numbers in binary.

**Formalization Note.** The weight block comes first and is length-prefixed, so the word is self-delimiting
(`encInstance`'s last block runs to the end of the word); the encoding is injective, proved in
`Solutions/verification/GyoriLovasz_Supplement_sanity.lean`. Weights are binary words, so a running time polynomial in
the input length is polynomial in the bit length of the weights, not in their values. -/
def encWInstance (I : WInstance) : List Sym :=
  encNum I.weights.length ++ I.weights.flatMap encNum ++ encInstance I.base

end Supplement

end GyoriLovasz


