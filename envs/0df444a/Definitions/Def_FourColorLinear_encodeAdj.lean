-- Prove2me | Definitions.Def_FourColorLinear_encodeAdj
-- name    : FourColorLinear_encodeAdj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:00.021058+00:00
-- url     : https://prove2.me/theorems/02b06602-15d5-4236-9ac1-d1f24d4f5db7
-- title:
--   Adjacency lists of a simple graph and their input words
-- statement:
--   Let $G$ be a simple graph on the vertices $\{0,\dots,n-1\}$. **Adjacency lists** of $G$ give for each vertex $v$ a list without repetition of exactly the neighbours of $v$, in any order. Their **input words** are $n$, followed for each vertex by its degree and its neighbours.
--
--   This is the input of the main theorem. It contains no embedding, and on a planar graph its length is $O(n)$ because the lists have no repetition.
-- source:
--   Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, Four-Coloring Planar Graphs in Linear Time, arXiv:2610.39753 (held version, sha256 4dce39c5…), Theorem 1, p.2

import Mathlib

namespace FourColorLinear

/-- `adj` lists the neighbours of each vertex of the simple graph `G`, without repetition and in any
order. This is the input of Theorem 1 of arXiv:2610.39753 (held version, sha256 4dce39c5…), p.2.

**Formalization Note** Theorem 1 names no input format. No embedding is given. `Nodup` is what makes
the input size `O(n)` on a planar graph. -/
def AdjacencyLists {n : ℕ} (G : SimpleGraph (Fin n)) (adj : Fin n → List (Fin n)) : Prop :=
  ∀ v, (adj v).Nodup ∧ ∀ u, u ∈ adj v ↔ G.Adj v u

/-- The input words of adjacency lists: `n`, then for each vertex its degree and its neighbours. -/
def encodeAdj {n : ℕ} (adj : Fin n → List (Fin n)) : List ℕ :=
  n :: (List.ofFn fun v => (adj v).length :: (adj v).map Fin.val).flatten

end FourColorLinear


