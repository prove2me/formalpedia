-- Prove2me | Definitions.Def_CNFEncComplexity_encNbrIn
-- name    : CNFEncComplexity_encNbrIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:32:17.582209+00:00
-- url     : https://prove2.me/theorems/393df326-e3eb-446f-a2a8-92951601ae35
-- title:
--   Input and output of the neighbor computation of Lemma 14
-- statement:
--   The neighbor computation of Lemma 14 receives $(N,k,\ell,i)$, the size $N=|L|$ of the universe, the parameter $k$, a left vertex $\ell<N$ and a neighbor index $i$, all in binary, as words. Its output, "no $i$-th neighbor" or a right vertex $\rho$, is written as one bit followed by $\rho$ in binary.
--
--   For $2^k\le N$, $\ell<N$ and $i<d$ the input length is $O(\lg N+\lg d)$, so time polynomial in the input length is time polynomial in $\lg|L|$ and $\lg d$.
-- source:
--   Krapivin, Przybocki, Subercaseaux, The CNF Encoding Complexity of Boolean Functions, arXiv:2611.05614 (held version, sha256 97421ce1…), Lemma 14, pp.13–14 (PDF 14–15)

import Mathlib
import Definitions.Def_CNFEncComplexity_encWords

namespace CNFEncComplexity

/-- An optional number as bits: `none ↦ [false]`, `some ρ ↦ true` followed by `ρ` in binary. -/
def encOptNat : Option ℕ → List Bool
  | none => [false]
  | some ρ => true :: binWord ρ

/-- **Input of the neighbor computation of Lemma 14.** Krapivin, Przybocki, Subercaseaux, *The CNF Encoding Complexity of Boolean Functions*, arXiv:2611.05614 (held version, sha256 97421ce1…), Lemma 14, pp.13–14 (PDF 14–15): "For each
left vertex, its ith neighbor can be computed deterministically in time polynomial in lg |L| and lg d,
where d is the maximum left degree."

`encNbrIn (N, k, ℓ, i)` writes the universe size `N = |L|`, the parameter `k`, the left vertex
`ℓ < N` and the neighbor index `i`, all in binary, as words.

**Formalization Note.** For `2^k ≤ N`, `ℓ < N` and `i < d`, the input length is `O(lg N + lg d)`, so
polynomial time in the input length is polynomial time in `lg |L|` and `lg d`. -/
def encNbrIn (x : ℕ × ℕ × ℕ × ℕ) : List (Fin 3) :=
  encWords [binWord x.1, binWord x.2.1, binWord x.2.2.1, binWord x.2.2.2]

end CNFEncComplexity


