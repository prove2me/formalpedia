-- Prove2me | Definitions.Def_EulerSparsify_RatDigraph
-- name    : EulerSparsify_RatDigraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:24.278216+00:00
-- url     : https://prove2.me/theorems/b5f23305-9636-4e2f-9204-f51a402794cb
-- title:
--   Finite input graph with rational weights
-- statement:
--   An input instance of the algorithms: a number $n$ of vertices $0,\dots,n-1$ and a list of edges $(h,t,q)$ with head (source) $h$, tail (target) $t$ and rational weight $q$. It is **well formed** if every endpoint is less than $n$ and every weight is nonnegative; then it describes the weighted directed graph on vertices $\{0,\dots,n-1\}$ whose edges are the positions of the list. Parallel edges and self-loops can be written.
--
--   **Formalization Note** "Polynomial time" is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime` over the published four-letter alphabet `OnlineCRS.Combine.Sym` (two bits, a separator inside a rational, a word separator). All numbers are written in binary (published `encNat`, `encInt`, `encRat`), so the length of an encoding is the usual bit size of the instance. Every list is preceded by its length and no word contains the word separator, so the encoding is injective.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Theorem 1.2, p.2; Proposition 4.3, p.13; Lemma 5.10, pp.21–22

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph
import Definitions.Def_EulerSparsify_joinW
import Definitions.Def_OnlineCRS_Combine_encRat

namespace EulerSparsify

/-- **A finite input graph with rational weights** (input of the algorithms of Theorem 1.2, p.2,
Proposition 4.3, p.13, and Lemma 5.10, pp.21–22).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Theorem 1.2: "such a sparsifier can be computed in polynomial time".

`(n, edges)`: vertices `0, …, n−1`; each entry `(h, t, q)` is an edge with head (source) `h`, tail
(target) `t` and weight `q`. Parallel edges and self-loops can be written.

**Formalization Note.** "Polynomial time" is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime` over the published alphabet `OnlineCRS.Combine.Sym = Fin 4`
(`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are binary (published
`OnlineCRS.Combine.encNat`, `encInt`, `encRat`), so the length of an encoding is the usual bit size.
Every list is preceded by its length and no word contains the separator `3`, so the encodings are
injective. -/
abbrev RatDigraph : Type := ℕ × List (ℕ × ℕ × ℚ)

/-- Well-formed: every endpoint is `< n` and every weight is `≥ 0`. -/
def RatDigraph.WellFormed (I : RatDigraph) : Prop :=
  ∀ x ∈ I.2, x.1 < I.1 ∧ x.2.1 < I.1 ∧ 0 ≤ x.2.2

/-- The graph on vertex type `Fin n` and edge type `Fin |edges|` described by a well-formed input. -/
def RatDigraph.toDiGraph (I : RatDigraph) (h : I.WellFormed) :
    DiGraph (Fin I.1) (Fin I.2.length) where
  head e := ⟨(I.2.get e).1, (h _ (List.get_mem _ _)).1⟩
  tail e := ⟨(I.2.get e).2.1, (h _ (List.get_mem _ _)).2.1⟩
  w e := ((I.2.get e).2.2 : ℝ)

/-- The words of an input graph: `n`, then the edge list (length first), each edge as head, tail,
weight. -/
def RatDigraph.tok (I : RatDigraph) : List (List OnlineCRS.Combine.Sym) :=
  OnlineCRS.Combine.encNat I.1 ::
    ReserveLB.tokList (fun x => [OnlineCRS.Combine.encNat x.1, OnlineCRS.Combine.encNat x.2.1,
      OnlineCRS.Combine.encRat x.2.2]) I.2

/-- The binary encoding of an input graph. -/
def encRatDigraph (I : RatDigraph) : List OnlineCRS.Combine.Sym :=
  joinW I.tok

end EulerSparsify


