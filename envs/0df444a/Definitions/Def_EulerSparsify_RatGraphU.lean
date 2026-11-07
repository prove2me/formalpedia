-- Prove2me | Definitions.Def_EulerSparsify_RatGraphU
-- name    : EulerSparsify_RatGraphU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:47.539267+00:00
-- url     : https://prove2.me/theorems/cee6dac1-1518-421c-932f-f082de9932b9
-- title:
--   Finite unweighted input graph
-- statement:
--   An input instance of the algorithm of Lemma 4.2: a number $n$ of vertices and a list of edges $(a,b)$. It is **well formed** if every endpoint is less than $n$; it then describes the unweighted graph (all weights $1$) on $\{0,\dots,n-1\}$ whose edges are the positions of the list. Parallel edges and self-loops can be written.
--
--   **Formalization Note** "Polynomial time" is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime` over the published four-letter alphabet `OnlineCRS.Combine.Sym` (two bits, a separator inside a rational, a word separator). All numbers are written in binary (published `encNat`, `encInt`, `encRat`), so the length of an encoding is the usual bit size of the instance. Every list is preceded by its length and no word contains the word separator, so the encoding is injective.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Lemma 4.2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph
import Definitions.Def_EulerSparsify_joinW

namespace EulerSparsify

/-- **A finite unweighted input graph** (input of the algorithm of Lemma 4.2, p.12, PDF p.14).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Lemma 4.2: "There is a polynomial time algorithm that given any unweighted graph G = (V, E)".

`(n, edges)`: vertices `0, …, n−1`; each entry `(a, b)` is an edge between `a` and `b` (parallel
edges and self-loops can be written).

**Formalization Note.** "Polynomial time" is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime` over the published alphabet `OnlineCRS.Combine.Sym = Fin 4`
(`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are binary (published
`OnlineCRS.Combine.encNat`, `encInt`, `encRat`), so the length of an encoding is the usual bit size.
Every list is preceded by its length and no word contains the separator `3`, so the encodings are
injective. -/
abbrev RatGraphU : Type := ℕ × List (ℕ × ℕ)

/-- Well-formed: every endpoint is `< n`. -/
def RatGraphU.WellFormed (I : RatGraphU) : Prop :=
  ∀ x ∈ I.2, x.1 < I.1 ∧ x.2 < I.1

/-- The unweighted graph (all weights `1`) described by a well-formed input. -/
def RatGraphU.toDiGraph (I : RatGraphU) (h : I.WellFormed) :
    DiGraph (Fin I.1) (Fin I.2.length) where
  head e := ⟨(I.2.get e).1, (h _ (List.get_mem _ _)).1⟩
  tail e := ⟨(I.2.get e).2, (h _ (List.get_mem _ _)).2⟩
  w _ := 1

/-- The words of an unweighted input graph: `n`, then the edge list (length first). -/
def RatGraphU.tok (I : RatGraphU) : List (List OnlineCRS.Combine.Sym) :=
  OnlineCRS.Combine.encNat I.1 ::
    ReserveLB.tokList (fun x => [OnlineCRS.Combine.encNat x.1, OnlineCRS.Combine.encNat x.2]) I.2

end EulerSparsify


