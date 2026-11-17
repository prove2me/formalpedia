-- Prove2me | Definitions.Def_UniqueOptScores_Supplement_UOCLIQUE
-- name    : UniqueOptScores_Supplement_UOCLIQUE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:54:31.659105+00:00
-- url     : https://prove2.me/theorems/7c82cd61-8a53-4254-9aa4-e350e09bf557
-- title:
--   The unique maximum clique problem $\mathrm{UOCLIQUE}$
-- statement:
--   $\mathrm{UOCLIQUE}$ asks whether exactly one clique of a graph $G$ attains the largest clique size $\omega(G)$ present in $G$. The size is not part of the input, and smaller cliques do not affect the answer. As a language: $w\in\mathrm{UOCLIQUE}$ if $w$ is the code of a graph $G$ on some $n$ vertices and there is exactly one vertex set $S$ such that
--   $$S\text{ is a clique of }G\quad\text{and}\quad |T|\le|S|\ \text{ for every clique } T \text{ of } G .$$
--   Cliques are pairwise adjacent vertex sets; the empty set and singletons are cliques. The graph with no vertices is a YES instance, and an edgeless graph on at least two vertices is a NO instance.
--
--   $\mathrm{UOCLIQUE}$ is the motivating problem of the paper; Theorem 1.1 places it outside $\mathrm{DP}$ unless $\mathrm{PH}=\mathrm S_2^{\mathrm{NP}}$.
--
--   **Formalization Note** Adjacency-matrix encoding (previous definition); words that are not graph codes are not in the language.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), §1.1, p.1 (PDF p.2)

import Mathlib
import Definitions.Def_UniqueOptScores_Supplement_graphOf

namespace UniqueOptScores

namespace Supplement

/-- **The unique maximum clique problem UOCLIQUE.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §1.1, p.1 (PDF p.2): "The unique maximum clique problem, UOCLIQUE, asks instead whether
exactly one clique attains the largest size present in G. Here the size is not specified in the
input, and smaller cliques do not affect the answer."

`w ∈ UOCLIQUE` if `w` is the code of a graph `G` on some `n` vertices (`IsGraphCode`) and exactly
one vertex set `S` is a clique of `G` of maximum size, i.e. a clique with `|T| ≤ |S|` for every
clique `T` of `G`.

**Formalization Note.** Adjacency-matrix encoding (`graphOf`); words that are not graph codes are
not in the language. Cliques are Mathlib's `SimpleGraph.IsClique` (pairwise adjacent vertex sets;
`∅` and singletons are cliques), so the empty graph (`n = 0`, the empty word) is a YES instance and
an edgeless graph on `n ≥ 2` vertices is a NO instance. The maximum is over all cliques of `G`;
`n` is determined by `|w| = n²`. -/
def UOCLIQUE : Set (List Bool) :=
  {w | ∃ n : ℕ, IsGraphCode n w ∧
    ∃! S : Finset (Fin n), (graphOf n w).IsClique (S : Set (Fin n)) ∧
      ∀ T : Finset (Fin n), (graphOf n w).IsClique (T : Set (Fin n)) → T.card ≤ S.card}

end Supplement

end UniqueOptScores


