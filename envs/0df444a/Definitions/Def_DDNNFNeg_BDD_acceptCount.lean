-- Prove2me | Definitions.Def_DDNNFNeg_BDD_acceptCount
-- name    : DDNNFNeg_BDD_acceptCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:21:44.362219+00:00
-- url     : https://prove2.me/theorems/a71db841-c403-4fa6-860b-19756ec82df4
-- title:
--   Number of accepting computations of a branching program
-- statement:
--   For a branching program $B$, an input $x \in \{0,1\}^X$ and a vertex $k$, the number of **accepting computations** from $k$ on $x$ is the number of sequences of guesses at $\vee$ vertices that lead from $k$ to a sink labelled $1$, where at a vertex labelled by a variable $v$ the outgoing edge labelled $x(v)$ is followed. A $1$-sink counts one computation, a $0$-sink none, a variable vertex counts what its $x(v)$-successor counts, and a $\vee$ vertex the sum over its two successors.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Definition 3.2, p.9

import Mathlib
import Definitions.Def_DDNNFNeg_BDD

namespace DDNNFNeg

/-- The number of accepting computations of the branching program `B` from vertex `k` on
the input `x` (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), Definition 3.2, p.9): the number of sequences of guesses at `∨` vertices
that lead from `k` to a sink labelled `1`, where at a variable vertex the edge labelled
`x v` is followed. A sink labelled `1` counts one, a sink labelled `0` zero, a variable vertex
counts what its `x v`-successor counts, and a `∨` vertex counts the sum over its two
successors. -/
def BDD.acceptCount {X : Type*} (B : BDD X) (x : X → Bool) (k : Fin B.size) : ℕ :=
  match h : B.node k with
  | .sink b => if b then 1 else 0
  | .test v lo hi =>
      have hlh := (B.wf k).1 v lo hi h
      if x v then B.acceptCount x hi else B.acceptCount x lo
  | .choice l r =>
      have hlr := (B.wf k).2 l r h
      B.acceptCount x l + B.acceptCount x r
termination_by B.size - k.val
decreasing_by
  · have := hlh.2; simp only [Fin.lt_def] at this; omega
  · have := hlh.1; simp only [Fin.lt_def] at this; omega
  · have := hlr.1; simp only [Fin.lt_def] at this; omega
  · have := hlr.2; simp only [Fin.lt_def] at this; omega

end DDNNFNeg


