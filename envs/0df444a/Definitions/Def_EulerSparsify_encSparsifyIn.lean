-- Prove2me | Definitions.Def_EulerSparsify_encSparsifyIn
-- name    : EulerSparsify_encSparsifyIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:33:23.786856+00:00
-- url     : https://prove2.me/theorems/57de5273-668b-4af7-bfba-17d4a5e327ff
-- title:
--   Encoding of an instance $(\vec G,\varepsilon,\delta)$ of Theorem 1.2
-- statement:
--   The input encoding of the sparsification algorithm of Theorem 1.2: the words of the input graph, then $\varepsilon$ and the failure probability $\delta$ as binary rationals. The variant with coins appends one word holding a string of coin bits; a randomized algorithm is a deterministic machine run on this longer input.
--
--   **Formalization Note** "Polynomial time" is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime` over the published four-letter alphabet `OnlineCRS.Combine.Sym` (two bits, a separator inside a rational, a word separator). All numbers are written in binary (published `encNat`, `encInt`, `encRat`), so the length of an encoding is the usual bit size of the instance. Every list is preceded by its length and no word contains the word separator, so the encoding is injective.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Theorem 1.2, p.2 (PDF p.4); Theorem 5.11, p.23

import Mathlib
import Definitions.Def_EulerSparsify_RatDigraph
import Definitions.Def_OnlineCRS_Combine_bit

namespace EulerSparsify

/-- **Encoding of an instance `(⃗G, ε, δ)` of Theorem 1.2** (p.2, PDF p.4).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Theorem 1.2: "such a sparsifier can be computed in polynomial time"; Theorem 5.11, p.23:
"ExistentialSparsify succeeds with high probability".

`encSparsifyIn (I, ε, δ)`: the words of the graph `I`, then `ε` and the failure probability `δ` as
rationals, joined by `3`.

**Formalization Note.** "Polynomial time" is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime` over the published alphabet `OnlineCRS.Combine.Sym = Fin 4`
(`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are binary (published
`OnlineCRS.Combine.encNat`, `encInt`, `encRat`), so the length of an encoding is the usual bit size.
Every list is preceded by its length and no word contains the separator `3`, so the encodings are
injective. -/
def encSparsifyIn (x : RatDigraph × ℚ × ℚ) : List OnlineCRS.Combine.Sym :=
  joinW (x.1.tok ++ [OnlineCRS.Combine.encRat x.2.1, OnlineCRS.Combine.encRat x.2.2])

/-- The instance followed by one word holding the coin bits (`0`, `1`): the input of a randomized
algorithm run with these coins. -/
def encSparsifyInCoins (x : (RatDigraph × ℚ × ℚ) × List Bool) : List OnlineCRS.Combine.Sym :=
  joinW (x.1.1.tok ++ [OnlineCRS.Combine.encRat x.1.2.1, OnlineCRS.Combine.encRat x.1.2.2,
    x.2.map OnlineCRS.Combine.bit])

end EulerSparsify


