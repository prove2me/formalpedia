-- Prove2me | Definitions.Def_QPACLarge_seedBits
-- name    : QPACLarge_seedBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:26.486045+00:00
-- url     : https://prove2.me/theorems/a14439bd-72dc-45af-895e-55d322ac8f72
-- title:
--   A seed as an $r$-bit string
-- statement:
--   The bit-string encoding of a seed lists $a_\emptyset$, then $a_1, \dots, a_n$, then the $a_{ij}$ ($i < j$) in lexicographic order of $(i, j)$: this identifies the seed set with $\{0,1\}^r$. It is the encoding on which "$J$ and its inverse are efficiently computable" (Lemma 3.1) is stated.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 3.1.1, p.19; Section 3.2.1, p.22

import Mathlib
import Definitions.Def_QPACLarge_Seed
import Definitions.Def_QAlgorithms_ClassicalStringComputability

namespace QPACLarge

open QAlgorithms.Complexity

/-- **A seed as an `r`-bit string.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 3.1.1, p.19 ("`a = (a_∅, {aᵢ}_{i=1}^n, {aᵢⱼ}_{1≤i<j≤n})`") and Section 3.2.1, p.22 ("the
seed set `A` is identified with `{0,1}^r`").

The bits `a_∅, a₁, …, aₙ`, then `aᵢⱼ` for `i < j` in lexicographic order of `(i, j)`. -/
def seedBits {n : ℕ} (a : Seed n) : Str :=
  a.1 :: (List.ofFn a.2.1 ++ (List.finRange n).flatMap fun i =>
    (List.finRange n).filterMap fun j => if h : i < j then some (a.2.2 ⟨(i, j), h⟩) else none)

end QPACLarge


