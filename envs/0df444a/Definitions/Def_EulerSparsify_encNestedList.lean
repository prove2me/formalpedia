-- Prove2me | Definitions.Def_EulerSparsify_encNestedList
-- name    : EulerSparsify_encNestedList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:33:52.958836+00:00
-- url     : https://prove2.me/theorems/f9bdf3e7-e9cc-4d6a-afa7-80f7e937ce25
-- title:
--   Encoding of a nested ER partitioning
-- statement:
--   The encoding of a nested family $\{K_i,F_i,b_i\}_{i\in[I]}$ as a list of members $(U_i, E_i, F_i, j_i)$: the vertex list of $K_i$, the edge numbers of $E_i$ and of $F_i$ (each list length first) and the integer $j_i$ with $b_i=2^{j_i}w_{\min}$. It is the output of the algorithm of Proposition 4.3 and part of the input of Algorithm 5.1. The helper `NestedFamily.ofList` reads such a list as a family on a given graph, ignoring numbers that name no vertex or edge.
--
--   **Formalization Note** "Polynomial time" is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime` over the published four-letter alphabet `OnlineCRS.Combine.Sym` (two bits, a separator inside a rational, a word separator). All numbers are written in binary (published `encNat`, `encInt`, `encRat`), so the length of an encoding is the usual bit size of the instance. Every list is preceded by its length and no word contains the word separator, so the encoding is injective.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Proposition 4.3, p.13 (PDF p.15); Algorithm 5.1, p.22

import Mathlib
import Definitions.Def_EulerSparsify_joinW
import Definitions.Def_EulerSparsify_NestedFamily
import Definitions.Def_OnlineCRS_Combine_encInt

namespace EulerSparsify

/-- The words of a nested-partitioning list: for each member, its vertex list, edge list `E_i`, owned
edge list `F_i` (each length first) and the exponent `j_i`. -/
def tokNested (l : List (List ℕ × List ℕ × List ℕ × ℤ)) : List (List OnlineCRS.Combine.Sym) :=
  ReserveLB.tokList (fun x => tokNatList x.1 ++ tokNatList x.2.1 ++ tokNatList x.2.2.1 ++
    [OnlineCRS.Combine.encInt x.2.2.2]) l

/-- **Encoding of a nested ER partitioning `{K_i, F_i, b_i}_{i∈[I]}`** (output of the algorithm of
Proposition 4.3, p.13, PDF p.15; input of Algorithm 5.1, p.22, PDF p.24).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Proposition 4.3: "computes in polynomial time a c_ner · n/m-nested ER partitioning".

Each member is `(vertices of K_i, edge indices of E_i, edge indices of F_i, j_i)` with
`b_i = 2^{j_i} w_min`.

**Formalization Note.** "Polynomial time" is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime` over the published alphabet `OnlineCRS.Combine.Sym = Fin 4`
(`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are binary (published
`OnlineCRS.Combine.encNat`, `encInt`, `encRat`), so the length of an encoding is the usual bit size.
Every list is preceded by its length and no word contains the separator `3`, so the encodings are
injective. -/
def encNestedList (l : List (List ℕ × List ℕ × List ℕ × ℤ)) : List OnlineCRS.Combine.Sym :=
  joinW (tokNested l)

/-- Read a list of members as a family `NestedFamily V E`, given the numbering `vIdx` of vertices
and `eIdx` of edges (numbers that name no vertex or edge are ignored). -/
def NestedFamily.ofList {V E : Type} [Fintype V] [Fintype E] (vIdx : V → ℕ) (eIdx : E → ℕ)
    (l : List (List ℕ × List ℕ × List ℕ × ℤ)) : NestedFamily V E where
  I := l.length
  U i := Finset.univ.filter fun v => vIdx v ∈ (l.get i).1
  Ed i := Finset.univ.filter fun e => eIdx e ∈ (l.get i).2.1
  F i := Finset.univ.filter fun e => eIdx e ∈ (l.get i).2.2.1
  j i := (l.get i).2.2.2

end EulerSparsify


