-- Prove2me | Definitions.Def_OptRobustCD_Layouts
-- name    : OptRobustCD_Layouts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:51:00.646043+00:00
-- url     : https://prove2.me/theorems/f1a893ed-dca2-4c67-a418-06a433c1c10c
-- title:
--   Input and output layouts: graph codes, values on directed edges, sparse edge vectors, $\{\pm1\}$-labellings
-- statement:
--   How graphs and vectors are written on the tape of the machine `OptRobustCD.Machine`.
--
--   1. A graph $G$ on $[n]$ with $m$ edges is the list $[n,m]$ followed by each edge once as a pair of vertex numbers, in any order and orientation ($\mathrm{GraphCode}$). Every statement quantifies over all encodings.
--   2. For Theorem 4.2, the graph code is followed, for each listed edge $(a,b)$ in the same order, by $Y_{a\to b}$ and $Y_{b\to a}$.
--   3. A vector $z$ on ordered pairs is output sparsely as triples $(u,v,z_{u\to v})$ over a duplicate-free list of ordered pairs outside of which $z$ vanishes. A dense output would take $n^2$ steps.
--   4. A $\{\pm1\}$-labelling of $n$ vertices is a list of $n$ reals, each $1$ or $-1$, read back as a labelling $\hat\sigma\in\{\pm1\}^n$.
--
--   **Formalization Note** Labellings are `Fin n → Bool` with `true ↦ +1`, the convention of the published `SBMThreshold_Main_Setting`.
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Theorem 1.1 p.2 (pdf p.4); Theorem 4.2 p.16 (pdf p.18); Lemma 5.3 p.25 (pdf p.27); Lemma 5.8 p.27 (pdf p.29); Theorem 5.1 p.24 (pdf p.26)

import Mathlib
import Definitions.Def_OptRobustCD_Machine
import Definitions.Def_OptRobustCD_DirEdges

namespace OptRobustCD

/-!
# Input and output layouts of the algorithms

Hopkins, Hua, Mohanty, Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027
submission (manuscript of November 3, 2026, sha256 3d287d54…): Theorem 1.1 (p.2, pdf p.4: the
algorithm "takes a graph G, returns a {±1}-labeling σ̂(G) of the vertices"), Theorem 4.2
(p.16, pdf p.18), Lemma 5.3 (p.25, pdf p.27: input `y ∈ R^n` and a graph `F`, output a vector
`ξ̂(F)` on directed edges), Lemma 5.8 (p.27, pdf p.29), Theorem 5.1 (p.24, pdf p.26).

**Formalization Note.**
* A graph `G` on `[n]` is given as `[n, m]` followed by each of its `m` edges once, as a pair of
  vertex indices, in any order and orientation (`GraphCode`). Every statement quantifies over all
  such encodings.
* `GraphValCode G Y l`: the graph code followed, for each listed edge `(a, b)` in the same order,
  by `Y_{a→b}, Y_{b→a}` (the input of BP in Theorem 4.2).
* A vector on directed edges is output sparsely, as triples `(u, v, z_{u→v})` over a duplicate-free
  list of ordered pairs outside of which `z` vanishes (`EVecCode`); a dense output would take
  `n²` steps.
* A `{±1}`-labelling is output as a list of `n` reals each equal to `1` or `−1`
  (`IsLabelling`); `labelOfList` reads it back as `Fin n → Bool` (`true ↦ +1`).
-/

open scoped Classical

/-- The flat list `[a₀, b₀, a₁, b₁, …]` of a list of vertex pairs. -/
def pairList {n : ℕ} (es : List (Fin n × Fin n)) : List ℝ :=
  (es.map fun p => [((p.1 : ℕ) : ℝ), ((p.2 : ℕ) : ℝ)]).flatten

/-- `es` lists every edge of `G` exactly once, each in some orientation. -/
def EdgeList {n : ℕ} (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n)) : Prop :=
  (es.map fun p => s(p.1, p.2)).Nodup ∧ ∀ e, e ∈ G.edgeSet ↔ ∃ p ∈ es, e = s(p.1, p.2)

/-- `l` encodes `G`: `[n, m]`, then each edge once as a pair of vertex indices, in any order and
orientation. -/
def GraphCode {n : ℕ} (G : SimpleGraph (Fin n)) (l : List ℝ) : Prop :=
  ∃ es : List (Fin n × Fin n), EdgeList G es ∧
    l = [(n : ℝ), ((es.length : ℕ) : ℝ)] ++ pairList es

/-- `l` encodes `G` together with values on its directed edges: the graph code, then for each
listed edge `(a, b)`, in the same order, `Y_{a→b}` and `Y_{b→a}`. -/
def GraphValCode {n : ℕ} (G : SimpleGraph (Fin n)) (Y : EVec n) (l : List ℝ) : Prop :=
  ∃ es : List (Fin n × Fin n), EdgeList G es ∧
    l = [(n : ℝ), ((es.length : ℕ) : ℝ)] ++ pairList es ++
      (es.map fun p => [Y (p.1, p.2), Y (p.2, p.1)]).flatten

/-- `l` encodes the vector `z` on ordered pairs sparsely: triples `(u, v, z_{u→v})` over a
duplicate-free list of ordered pairs outside of which `z` vanishes. -/
def EVecCode {n : ℕ} (z : EVec n) (l : List ℝ) : Prop :=
  ∃ es : List (Fin n × Fin n), es.Nodup ∧ (∀ p, p ∉ es → z p = 0) ∧
    l = (es.map fun p => [((p.1 : ℕ) : ℝ), ((p.2 : ℕ) : ℝ), z p]).flatten

/-- `l` is a `{±1}`-labelling of `n` vertices: `n` entries, each `1` or `−1`. -/
def IsLabelling (n : ℕ) (l : List ℝ) : Prop :=
  l.length = n ∧ ∀ x ∈ l, x = 1 ∨ x = -1

/-- The labelling `Fin n → Bool` read from a list (`true` iff the entry is `1`). -/
noncomputable def labelOfList (n : ℕ) (l : List ℝ) : Fin n → Bool :=
  fun v => decide (l.getD v 0 = 1)

end OptRobustCD


