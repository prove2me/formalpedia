-- Prove2me | Definitions.Def_EulerSparsify_encHalfStepIn
-- name    : EulerSparsify_encHalfStepIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:35:01.115967+00:00
-- url     : https://prove2.me/theorems/4d04d410-ebd6-4a84-96e5-7e50e15a328f
-- title:
--   Encoding of an input of Algorithm 5.1
-- statement:
--   The input encoding of Algorithm 5.1 (ExistentialDecompSparsify): the words of the input graph, of the nested ER partitioning of its support graph (edge numbers index the input's edge list), and the failure probability $\delta$ as a binary rational. The variant with coins appends one word of coin bits.
--
--   **Formalization Note** "Polynomial time" is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime` over the published four-letter alphabet `OnlineCRS.Combine.Sym` (two bits, a separator inside a rational, a word separator). All numbers are written in binary (published `encNat`, `encInt`, `encRat`), so the length of an encoding is the usual bit size of the instance. Every list is preceded by its length and no word contains the word separator, so the encoding is injective. The parameter $\varepsilon\in(0,1/100)$ of Algorithm 5.1 is never used by the algorithm and is not an input.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Algorithm 5.1, line 1 and p.22 (PDF p.24)

import Mathlib
import Definitions.Def_EulerSparsify_RatDigraph
import Definitions.Def_EulerSparsify_encNestedList
import Definitions.Def_OnlineCRS_Combine_bit

namespace EulerSparsify

/-- **Encoding of an input of Algorithm 5.1 (ExistentialDecompSparsify)** (p.22, PDF p.24).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Algorithm 5.1, line 1: "Input: a simple ⃗G = (V, E, w) and {K_i, F_i, b_i}_{i∈[I]} is a
ρ-nested ER partitioning of (V, supp(w), w_supp(w)), ε ∈ (0, 1/100)"; p.22: "ExistentialDecompSparsify
is implementable in poly(n, log U, log 1/δ) time."

`encHalfStepIn (I, P, δ)`: the words of the graph, of the partitioning (edge numbers index the
edge list of `I`) and the failure probability `δ`, joined by `3`.

**Formalization Note.** "Polynomial time" is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime` over the published alphabet `OnlineCRS.Combine.Sym = Fin 4`
(`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are binary (published
`OnlineCRS.Combine.encNat`, `encInt`, `encRat`), so the length of an encoding is the usual bit size.
Every list is preceded by its length and no word contains the separator `3`, so the encodings are
injective. The unused parameter `ε` of Algorithm 5.1 is not an input. -/
def encHalfStepIn (x : RatDigraph × List (List ℕ × List ℕ × List ℕ × ℤ) × ℚ) :
    List OnlineCRS.Combine.Sym :=
  joinW (x.1.tok ++ tokNested x.2.1 ++ [OnlineCRS.Combine.encRat x.2.2])

/-- The input followed by one word holding the coin bits. -/
def encHalfStepInCoins (x : (RatDigraph × List (List ℕ × List ℕ × List ℕ × ℤ) × ℚ) × List Bool) :
    List OnlineCRS.Combine.Sym :=
  joinW (x.1.1.tok ++ tokNested x.1.2.1 ++ [OnlineCRS.Combine.encRat x.1.2.2,
    x.2.map OnlineCRS.Combine.bit])

end EulerSparsify


