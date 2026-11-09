-- Prove2me | Definitions.Def_GroupIsoPoly_encAnswer
-- name    : GroupIsoPoly_encAnswer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:50:51.70805+00:00
-- url     : https://prove2.me/theorems/f6aa3ca3-2db8-4024-a29b-9c66372db9c3
-- title:
--   Binary code of a coset answer
-- statement:
--   Write each group element of an answer as a finite list of natural numbers (labels, permutation images, or matrix entries in field coordinates). The **code of an answer** is the single bit $0$ for emptiness; for a representative $u$ with generators $x_1,\dots,x_k$ it is the bit $1$, then the code of $u$, the number $k$, and the codes of $x_1,\dots,x_k$, where a list of numbers is coded by its length followed by its entries, all with the self-delimiting code of natural numbers.
--
--   The code is prefix-free, so the output of an algorithm determines its answer.
--
--   **Formalization Note** Numbers use the published `ExponomialAssortment.FPTAS.encodeNat`. Elements are output as themselves rather than as straight-line programs in the input generators (the paper's §3.5, p.19); for permutation and matrix groups each form is computable from the other in polynomial time.
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 8.1, p.71 (PDF p.75); §3.5, p.19 (PDF p.23)

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine

set_option autoImplicit false

namespace GroupIsoPoly

open ExponomialAssortment.FPTAS (encodeNat)

/-- The self-delimiting code of a list of natural numbers: its length, then its entries, each by
`encodeNat`. -/
def encNatList (l : List ℕ) : List Bool :=
  encodeNat l.length ++ (l.map encodeNat).flatten

/-- **The binary code of a coset answer.**

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 8.1, p.71 (PDF p.75): "The output is
emptiness, or a representative u and generators of Stab".

Group elements are first written as lists of natural numbers (labels, permutation images, matrix
entries in field coordinates). Emptiness is the single bit `0`; a representative `u` with a list of
generators is the bit `1`, the code of `u`, the number of generators, and the code of each generator.

**Formalization Note.** Numbers are written with the published
`ExponomialAssortment.FPTAS.encodeNat`; the code is prefix-free, so the output determines the
answer. Elements are output as themselves, not as straight-line programs in the input generators
(the paper's §3.5, p.19); for permutation and matrix groups the two forms are interconvertible in
polynomial time. -/
def encAnswer : Option (List ℕ × List (List ℕ)) → List Bool
  | none => [false]
  | some (u, gs) => true :: (encNatList u ++ encodeNat gs.length ++ (gs.map encNatList).flatten)

end GroupIsoPoly


