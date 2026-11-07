-- Prove2me | Definitions.Def_EulerSparsify_encLevelIn
-- name    : EulerSparsify_encLevelIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:33:35.941345+00:00
-- url     : https://prove2.me/theorems/d8cd3158-f696-4890-8694-382362898e3f
-- title:
--   Encoding of an instance $(G,\beta,p,\eta)$ of Lemma 4.2
-- statement:
--   The input encoding of the algorithm of Lemma 4.2: the words of the unweighted input graph, then the parameters $\beta$, $p$, $\eta$ as binary rationals.
--
--   **Formalization Note** "Polynomial time" is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime` over the published four-letter alphabet `OnlineCRS.Combine.Sym` (two bits, a separator inside a rational, a word separator). All numbers are written in binary (published `encNat`, `encInt`, `encRat`), so the length of an encoding is the usual bit size of the instance. Every list is preceded by its length and no word contains the word separator, so the encoding is injective.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Lemma 4.2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_EulerSparsify_RatGraphU
import Definitions.Def_OnlineCRS_Combine_encRat

namespace EulerSparsify

/-- **Encoding of an instance `(G, β, p, η)` of Lemma 4.2** (p.12, PDF p.14).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Lemma 4.2: "given any unweighted graph G = (V, E), with n = |V| and m = |E|, and parameters
β > 0, p ∈ (1/2, 1) and η ∈ (0, 1)".

The words of the graph, then `β`, `p`, `η` as rationals, joined by `3`.

**Formalization Note.** "Polynomial time" is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime` over the published alphabet `OnlineCRS.Combine.Sym = Fin 4`
(`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are binary (published
`OnlineCRS.Combine.encNat`, `encInt`, `encRat`), so the length of an encoding is the usual bit size.
Every list is preceded by its length and no word contains the separator `3`, so the encodings are
injective. -/
def encLevelIn (x : RatGraphU × ℚ × ℚ × ℚ) : List OnlineCRS.Combine.Sym :=
  joinW (x.1.tok ++ [OnlineCRS.Combine.encRat x.2.1, OnlineCRS.Combine.encRat x.2.2.1,
    OnlineCRS.Combine.encRat x.2.2.2])

end EulerSparsify


