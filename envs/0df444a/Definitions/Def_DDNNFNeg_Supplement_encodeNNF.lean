-- Prove2me | Definitions.Def_DDNNFNeg_Supplement_encodeNNF
-- name    : DDNNFNeg_Supplement_encodeNNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:47:56.907418+00:00
-- url     : https://prove2.me/theorems/63cc29d5-5351-448c-9e57-6c32114f6b7a
-- title:
--   Binary encoding of an NNF
-- statement:
--   An NNF over the variables $x_0, \dots, x_{n-1}$ with gates $g_0, \dots, g_{s-1}$ and output gate $g_o$ is encoded as a binary string listing $n$, $s$, $o$, and then each gate in order: a two-bit tag ($00$ literal, $01$ constant, $10$ $\wedge$, $11$ $\vee$) followed by the variable index and the polarity bit, the constant bit, or the two child indices. All numbers are written in self-delimiting binary.
--
--   This is the input format of the algorithms in Theorem 4.1.
--
--   **Formalization Note** The encoding is injective and has length $O(s \log(n+s) + \log n)$, polynomial in $n + s$, with no unary padding.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §4, p.10

import Mathlib
import Definitions.Def_DDNNFNeg_NNF
import Definitions.Def_PolyEvalDS_LargeChar_Encoding

namespace DDNNFNeg.Supplement

open PolyEvalDS.LargeChar

/-- The binary encoding of an NNF over the variables `Fin n` given to an algorithm
(Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §4, p.10): the number of variables `n`, the number of gates, the index of the output gate,
and then each gate in order: a 2-bit tag (`00` literal, `01` constant, `10` `∧`, `11` `∨`)
followed by the variable index and polarity bit (literal), the constant bit (constant), or the
two child indices (`∧`, `∨`), all numbers in self-delimiting binary (the published `PolyEvalDS.LargeChar.encNat`: each bit `b`
of `Nat.bits m`, least significant first, written `1 b`, then a final `0`).

**Formalization Note** The encoding is injective and its length is
`O(size · log(n + size) + log n)`, polynomial in `n + size`; it involves no unary padding. -/
def encodeNNF {n : ℕ} (C : NNF (Fin n)) : List Bool :=
  encNat n ++ encNat C.size ++ encNat C.out.val ++
    (List.ofFn fun k : Fin C.size =>
      match C.gate k with
      | .lit v pos => [false, false] ++ encNat v.val ++ [pos]
      | .const b => [false, true, b]
      | .and i j => [true, false] ++ encNat i.val ++ encNat j.val
      | .or i j => [true, true] ++ encNat i.val ++ encNat j.val).flatten

end DDNNFNeg.Supplement


