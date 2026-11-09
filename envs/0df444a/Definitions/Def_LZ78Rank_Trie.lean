-- Prove2me | Definitions.Def_LZ78Rank_Trie
-- name    : LZ78Rank_Trie
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:46:05.418142+00:00
-- url     : https://prove2.me/theorems/75030cfa-8c8b-43bc-b613-b169e99610dd
-- title:
--   The LZ78 trie as an edge-labelled rooted tree on $[0\,.\,.\,z]$
-- statement:
--   A rooted tree on the vertex set $[0\,.\,.\,z]$ with root $0$ is given by a parent map $\mathrm{par}$ and an edge-label map $\mathrm{lab}$ on the vertices $1,\dots,z$, with $\mathrm{par}(i)<i$: the edge between $i$ and its parent carries the label $\mathrm{lab}(i)$. The word read on the root-to-$i$ path is $\mathrm{pathWord}(0)=\varepsilon$ and $\mathrm{pathWord}(i)=\mathrm{pathWord}(\mathrm{par}(i))\cdot\mathrm{lab}(i)$.
--
--   The tree $(\mathrm{par},\mathrm{lab})$ is an **LZ78 trie** $\mathcal T_{78}(T)$ of a string $T$ over $\{1,\dots,\sigma\}$ (Observation 3.1) when, with $z=z_{78}(T)$,
--
--   1. $\mathrm{par}(i)<i$ for every $i\in[1\,.\,.\,z]$, so the vertex set is $[0\,.\,.\,z]$ with root $0$;
--   2. every edge label $\mathrm{lab}(i)$, $i\in[1\,.\,.\,z]$, lies in $[1\,.\,.\,\sigma]$;
--   3. for each $i\in[0\,.\,.\,z]$ the labels on the root-to-$i$ path read the phrase $f_i$.
--
--   **Formalization Note** "Trie" is read as an edge-labelled rooted tree: siblings need not carry distinct labels, because for $T=11$ the last phrase repeats $f_1$. Parents are numbered below their children ($\mathrm{par}(i)<i$), which is the shape Proposition 3.2's construction produces (the parent of $i$ is $p_i<i$). The path word is computed with fuel $i$, enough because parents strictly decrease.
-- source:
--   De–Kempa, Near-Optimal Compressed Algorithms and Data Structures by Eliminating Recursive Substructures, STOC 2027 submission (manuscript sha256 db4050af4e62ca74150f041d554ea7b206351a0c4ce7a37cb017488d6330ec6d), Observation 3.1 and Proposition 3.2, p.13 (PDF p.13); rooted trees, Section 2.2, p.9

import Mathlib
import Definitions.Def_LZ78Rank_LZ78

set_option autoImplicit false

namespace LZ78Rank

/-!
# The LZ78 trie as an edge-labelled rooted tree

De–Kempa, *Near-Optimal Compressed Algorithms and Data Structures by Eliminating Recursive
Substructures*, STOC 2027 submission (manuscript sha256 db4050af4e62…330ec6d), Observation 3.1
and Proposition 3.2, p.13 (= PDF p.13).

**Formalization Note.**
* A rooted tree on the vertex set `[0 . . z]` with root `0` is given by a parent map `par` and an
  edge-label map `lab` on the vertices `1, …, z`: the edge between a non-root vertex `i` and its
  parent `par i` carries the label `lab i`. Parents are required to satisfy `par i < i`, which
  makes the parent map acyclic, keeps it inside `[0 . . z]`, and makes every vertex reach the
  root; this is the shape Proposition 3.2's construction outputs ("the parent of i in T78(T) is
  pᵢ, and the edge (pᵢ → i) has the label cᵢ", with `pᵢ < i`).
* "Trie" is read as an edge-labelled rooted tree: siblings are **not** required to carry distinct
  labels. With distinct sibling labels Observation 3.1 would be false for `T = 11`, whose last
  phrase repeats `f₁` (Remark 2.12).
* `pathWord par lab i` is the word read on the root-to-`i` path. It is computed with fuel `i`,
  which suffices because parents strictly decrease; if the parent map ever fails to decrease the
  word is cut off (this never happens under `IsLZ78Trie`).
-/

/-- The labels on the path from the root `0` to the vertex `i`, with fuel. -/
def pathWordAux (par lab : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, i =>
    if 0 < i ∧ par i < i then pathWordAux par lab fuel (par i) ++ [lab i] else []

/-- The word read on the edges of the root-to-`i` path of the tree `(par, lab)`. -/
def pathWord (par lab : ℕ → ℕ) (i : ℕ) : List ℕ := pathWordAux par lab i i

/-- **The LZ78 trie** `T₇₈(T)` (Observation 3.1, p.13): `(par, lab)` is a rooted tree on the
vertex set `[0 . . z]`, `z = z₇₈(T)`, with root `0` (parents `par i < i`), every edge between a
non-root vertex and its parent has a label in `[1 . . σ]`, and for each `i ∈ [0 . . z]` the labels
on the root-to-`i` path read the phrase `fᵢ`. -/
def IsLZ78Trie (σ : ℕ) (T : List ℕ) (par lab : ℕ → ℕ) : Prop :=
  (∀ i : ℕ, 1 ≤ i → i ≤ z78 T → par i < i ∧ 1 ≤ lab i ∧ lab i ≤ σ) ∧
    ∀ i : ℕ, i ≤ z78 T → pathWord par lab i = phrase T i

end LZ78Rank


