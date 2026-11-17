-- Prove2me | Definitions.Def_UniqueOptScores_Supplement_graphOf
-- name    : UniqueOptScores_Supplement_graphOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:53:58.8082+00:00
-- url     : https://prove2.me/theorems/40b183ef-fba9-4919-bcd7-8bc6d3e6155e
-- title:
--   Graphs encoded by adjacency matrices
-- statement:
--   A word $w\in\{0,1\}^*$ is the **code of a graph on $n$ vertices** if $|w|=n^2$ and, read row by row as an $n\times n$ matrix (entry $(i,j)$ is bit $i\cdot n+j$, vertices $0,\dots,n-1$), it is symmetric with zero diagonal. The graph $G_n(w)$ read from $w$ has vertex set $\{0,\dots,n-1\}$ and an edge between distinct $i,j$ when entry $(i,j)$ or $(j,i)$ is $1$; on a graph code these are exactly the $1$ entries.
--
--   This is the input encoding of the unique maximum clique problem.
--
--   **Formalization Note** The paper fixes no graph encoding. Any two polynomial-time equivalent encodings whose validity is polynomial-time decidable give the same complexity statements.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), §1.1, p.1 (PDF p.2), input graph of UOCLIQUE

import Mathlib

namespace UniqueOptScores

namespace Supplement

/-- A word `w` is the **code of a graph on `n` vertices** if it has length `n²` and, read
row-major as an `n × n` 0/1 matrix (entry `(i, j)` is bit `i·n + j`), is symmetric with zero
diagonal. -/
def IsGraphCode (n : ℕ) (w : List Bool) : Prop :=
  w.length = n * n ∧
    (∀ i j : Fin n, w.getD (i.val * n + j.val) false = w.getD (j.val * n + i.val) false) ∧
    ∀ i : Fin n, w.getD (i.val * n + i.val) false = false

/-- **The graph on vertex set `Fin n` read from a word.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §1.1, p.1 (PDF p.2): UOCLIQUE takes a graph `G` as input.

`graphOf n w` has an edge between distinct `i` and `j` when bit `i·n + j` or bit `j·n + i` of `w`
is `1`.

**Formalization Note.** The paper fixes no graph encoding; this is the adjacency-matrix encoding
(any two polynomial-time equivalent encodings with polynomial-time decidable validity give the same
complexity statements). On a code (`IsGraphCode n w`) the edges are exactly the `1` entries of the
matrix. -/
def graphOf (n : ℕ) (w : List Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j => w.getD (i.val * n + j.val) false = true)

end Supplement

end UniqueOptScores


