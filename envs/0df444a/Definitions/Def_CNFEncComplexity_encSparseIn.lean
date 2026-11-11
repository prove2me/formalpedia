-- Prove2me | Definitions.Def_CNFEncComplexity_encSparseIn
-- name    : CNFEncComplexity_encSparseIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:32:30.587358+00:00
-- url     : https://prove2.me/theorems/4bbb10e4-bf38-417a-ba50-bde07d5d911d
-- title:
--   Input of the construction of Lemma 13
-- statement:
--   The construction of Lemma 13 receives $n$ in unary and the list $L$ of the elements of $f^{-1}(1)$, each a bit string of length $n$, as words.
--
--   For $M=|L|\ge1$ the input length is $(n+1)(M+1)+1$, so "time polynomial in $nM$" becomes time polynomial in the input length.
-- source:
--   Krapivin, Przybocki, Subercaseaux, The CNF Encoding Complexity of Boolean Functions, arXiv:2611.05614 (held version, sha256 97421ce1…), Lemma 13, pp.12–13 (PDF 13–14)

import Mathlib
import Definitions.Def_CNFEncComplexity_encWords

namespace CNFEncComplexity

/-- **Input of the construction of Lemma 13.** Krapivin, Przybocki, Subercaseaux, *The CNF Encoding Complexity of Boolean Functions*, arXiv:2611.05614 (held version, sha256 97421ce1…), Lemma 13, pp.12–13 (PDF 13–14): "Given the list
of elements of f⁻¹(1), an encoding attaining this bound can be constructed deterministically in time
polynomial in nM."

`encSparseIn (n, L)` writes `n` in unary and then each vector of the list `L` as a word.

**Formalization Note.** For `M = L.length ≥ 1` vectors of length `n`, the input length is
`(n + 1)(M + 1) + 1`, which is polynomial in `nM` up to the additive `n + M`; "polynomial in
`nM`" is read as polynomial in the input length. -/
def encSparseIn (x : ℕ × List (List Bool)) : List (Fin 3) :=
  encWords (unaryWord x.1 :: x.2)

end CNFEncComplexity


