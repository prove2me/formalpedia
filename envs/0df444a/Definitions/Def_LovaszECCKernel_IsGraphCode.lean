-- Prove2me | Definitions.Def_LovaszECCKernel_IsGraphCode
-- name    : LovaszECCKernel_IsGraphCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:04.512493+00:00
-- url     : https://prove2.me/theorems/da645021-7fdd-4beb-93d2-2aa75349c80e
-- title:
--   Input and output codes: edge lists, adjacency matrices, pair lists
-- statement:
--   The word-RAM programs of the mission read and write lists of natural numbers.
--
--   1. An **edge-list code** of a graph $G$ on $\{0,\dots,n-1\}$ with $m$ edges is $n, m$ followed by the edges $uv$, $u<v$, each once and in any order (the input of the kernel, read in time $O(n+m)$).
--   2. The **adjacency-matrix code** is $n$ followed by the $n^2$ entries of the adjacency matrix in row-major order (the input of Cluster Editing, read in time $O(n^2)$).
--   3. A **pair-list code** of a set $M$ of pairs of distinct vertices is $|M|$ followed by its pairs $(u,v)$, $u<v$, each once and in any order (the output of the Cluster Editing algorithms).
--
--   **Formalization Note** Every order of an edge list is a code, and statements quantify over all of them.
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Theorem 3, p.4, Proposition 1, p.17, and Lemma 2, p.21 (= PDF pp.4, 17, 21)

import Mathlib

set_option autoImplicit false

namespace LovaszECCKernel

/-- `c` is an **edge-list code of the graph** `G` on `Fin n` (Fomin, Golovach, Khargeliia,
Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic Extensions of the Lovász and
Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript sha256 a9d53ab8…), Theorem 3, p.4
(= PDF p.4): an input graph `G` with `n` vertices and `m` edges, read in time `O(n + m)`): `n`, the
number `m` of edges, and the edges `{v, w}` (each once, as `v < w`, in any order).

**Formalization Note** Copied from the `SNPTreedepth.IsGraphCode` draft (Depian et al.). Every order
of the edge list is a code, and statements quantify over all of them. -/
def IsGraphCode {n : ℕ} (G : SimpleGraph (Fin n)) (c : List ℕ) : Prop :=
  ∃ E : List (Fin n × Fin n), E.Nodup ∧ (∀ e ∈ E, e.1 < e.2) ∧
    (∀ v w : Fin n, v < w → (G.Adj v w ↔ (v, w) ∈ E)) ∧
    c = n :: E.length :: E.flatMap (fun e => [e.1.val, e.2.val])

open Classical in
/-- `c` is the **adjacency-matrix code** of the graph `G` on `Fin n` (Fomin et al., STOC 2027
submission (manuscript sha256 a9d53ab8…), Proposition 1, p.17 (= PDF p.17), where the input of
Cluster Editing is a graph read in time `O(n²)`): `n`, followed by the `n²` entries of the adjacency
matrix in row-major order, `1` for adjacent and `0` for non-adjacent. -/
def IsAdjMatrixCode {n : ℕ} (G : SimpleGraph (Fin n)) (c : List ℕ) : Prop :=
  c = n :: (List.finRange n).flatMap (fun u => (List.finRange n).map (fun v =>
    if G.Adj u v then 1 else 0))

/-- `out` is a **pair-list code** of the set `M` of pairs of distinct vertices of `Fin n` (Fomin et
al., STOC 2027 submission (manuscript sha256 a9d53ab8…), Proposition 1, p.17, and Lemma 2, p.21
(= PDF pp.17, 21), whose algorithms output a set `M ⊆ (V(G) choose 2)`): `|M|` followed by the
pairs `(u, v)`, `u < v`, each once, in any order.

**Formalization Note** The code also certifies that `M` contains no diagonal pair. -/
def IsPairListCode {n : ℕ} (M : Finset (Sym2 (Fin n))) (out : List ℕ) : Prop :=
  ∃ E : List (Fin n × Fin n), E.Nodup ∧ (∀ e ∈ E, e.1 < e.2) ∧
    (∀ e ∈ M, ¬ e.IsDiag) ∧ (∀ u v : Fin n, u < v → (s(u, v) ∈ M ↔ (u, v) ∈ E)) ∧
    out = E.length :: E.flatMap (fun e => [e.1.val, e.2.val])

end LovaszECCKernel


