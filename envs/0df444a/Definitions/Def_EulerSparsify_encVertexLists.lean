-- Prove2me | Definitions.Def_EulerSparsify_encVertexLists
-- name    : EulerSparsify_encVertexLists
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:28.073284+00:00
-- url     : https://prove2.me/theorems/b7b61c2d-f59a-4e71-ace2-05203d022628
-- title:
--   Encoding of a vertex partition $\{U_i\}_{i\in[I]}$
-- statement:
--   The output encoding of the algorithm of Lemma 4.2: a list of vertex lists, each written length first. The helper `partsOfLists` reads the $i$-th list as a set of vertices of $\{0,\dots,n-1\}$ (numbers $\ge n$ are ignored).
--
--   **Formalization Note** "Polynomial time" is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime` over the published four-letter alphabet `OnlineCRS.Combine.Sym` (two bits, a separator inside a rational, a word separator). All numbers are written in binary (published `encNat`, `encInt`, `encRat`), so the length of an encoding is the usual bit size of the instance. Every list is preceded by its length and no word contains the word separator, so the encoding is injective.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Lemma 4.2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_EulerSparsify_joinW

namespace EulerSparsify

/-- **Encoding of a vertex partition `{U_i}_{i∈[I]}`** (output of the algorithm of Lemma 4.2, p.12,
PDF p.14), written as a list of vertex lists.
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Lemma 4.2: "computes a partitioning {U_i}_{i∈[I]} of the vertices".

**Formalization Note.** "Polynomial time" is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime` over the published alphabet `OnlineCRS.Combine.Sym = Fin 4`
(`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are binary (published
`OnlineCRS.Combine.encNat`, `encInt`, `encRat`), so the length of an encoding is the usual bit size.
Every list is preceded by its length and no word contains the separator `3`, so the encodings are
injective. -/
def encVertexLists (l : List (List ℕ)) : List OnlineCRS.Combine.Sym :=
  joinW (ReserveLB.tokList tokNatList l)

/-- Read the `i`-th part of a list of vertex lists as a set of vertices of `Fin n` (indices
`≥ n` are ignored). -/
def partsOfLists (n : ℕ) (l : List (List ℕ)) (i : Fin l.length) : Finset (Fin n) :=
  Finset.univ.filter fun v => v.val ∈ l.get i

end EulerSparsify


