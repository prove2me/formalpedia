-- Prove2me | Definitions.Def_LocalBreadth_Supplement_IsProtectedTree
-- name    : LocalBreadth_Supplement_IsProtectedTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:21:50.82949+00:00
-- url     : https://prove2.me/theorems/1c91f4e1-da0d-462b-b260-a70e8f14d1a9
-- title:
--   $q$-protected trees
-- statement:
--   Let $K\in\mathcal X$ and $q:\mathcal X\to[0,1]$. A **$q$-protected tree rooted at $K$** is a countable rooted tree whose vertices $v$ carry a language $L_v\in\mathcal X$, a finite protected set $P_v\subseteq L_v$, a cutoff $s_v\ge1$ and a radius $a_v\ge0$, such that the root is labelled $K$, every child $w$ of $v$ has $L_w\subsetneq L_v$ and $a_w>a_v$, and
--   1. for every vertex $v$ and every $M\in\mathcal X$ with $P_v\subseteq M\subsetneq L_v$, $v$ has a child labelled $M$;
--   2. for every finite root-to-vertex path $v_0,\dots,v_r$, the chain $L_{v_0}\supsetneq\dots\supsetneq L_{v_r}$ is geometrically $q$-feasible at the cutoffs $s_{v_0},\dots,s_{v_r}$ outside $[-a_{v_r},a_{v_r}]^d\cap\mathbb Z^d$.
--
--   The tree may have infinite paths and leaves, and a language may label several vertices. Protected trees are the static certificates of §7: by Theorem 7.1 they exist for all targets exactly when the quotas are (up to $\varepsilon$) achievable.
--
--   **Formalization Note** Vertices are finite sequences of natural numbers (root `[]`, children `v ++ [n]`), so the tree is countable; the path to $v$ is its sequence of prefixes. The definition is stated for $\mathbb Z^d$.
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc309339291b1a61b8504342f4050ece6e4e903dd18b2bf541446f1064), Definition 7.5, pp.55–56

import Mathlib
import Definitions.Def_LocalBreadth_Supplement_IsGeomFeasible

namespace LocalBreadth.Supplement

/-- A rooted tree with vertex data, vertices being finite sequences of child indices: `[]` is the root,
and `v ++ [n]` is the `n`-th child of `v`. Each vertex carries a language label, a finite protected set,
a cutoff and a radius (Definition 7.5). -/
structure DecoratedTree (P : Type) where
  /-- The vertex set: a prefix-closed set of finite sequences containing the root `[]`. -/
  verts : Set (List ℕ)
  root_mem : [] ∈ verts
  prefix_mem : ∀ v ∈ verts, ∀ u, u <+: v → u ∈ verts
  /-- The language label `L_v`. -/
  lang : List ℕ → Set P
  /-- The protected set `P_v`. -/
  prot : List ℕ → Finset P
  /-- The cutoff `s_v`. -/
  cut : List ℕ → ℝ
  /-- The radius `a_v`. -/
  rad : List ℕ → ℝ

/-- A **q-protected tree** rooted at `K`. Kleinberg, Wei, STOC 2027 submission (manuscript sha256
f924cbfc…), Definition 7.5, pp.55–56: a countable rooted tree whose vertices carry a language label
`L_v ∈ X`, a finite protected set `P_v ⊆ L_v`, a cutoff `s_v ≥ 1` and a radius `a_v ≥ 0`; the root is
labelled `K`; a child `w` of `v` has `L_w ⊊ L_v` and `a_w > a_v`; and
1. for every vertex `v` and every `M ∈ X` with `P_v ⊆ M ⊊ L_v`, `v` has a child labelled `M`;
2. for every finite root-to-vertex path `v_0, …, v_r`, the chain `L_{v_0} ⊋ ⋯ ⊋ L_{v_r}` is
   geometrically `q`-feasible at the cutoffs `s_{v_0}, …, s_{v_r}` outside `[-a_{v_r}, a_{v_r}]^d ∩ ℤ^d`.

**Formalization Note.** Vertices are finite sequences of natural numbers, so the tree is countable;
every countable rooted tree is of this form. The tree need not be well-founded (infinite paths are
allowed), and a vertex may be a leaf. The root-to-vertex path of `v` is `v.take 0, …, v.take v.length`.
The quota at level `i` is `q(L_{v_i})`. -/
def IsProtectedTree {d : ℕ} (h : ℕ → ℝ) (q : Set (Fin d → ℤ) → ℝ) (X : Set (Set (Fin d → ℤ)))
    (K : Set (Fin d → ℤ)) (T : DecoratedTree (Fin d → ℤ)) : Prop :=
  T.lang [] = K ∧
  (∀ v ∈ T.verts, T.lang v ∈ X ∧ (T.prot v : Set (Fin d → ℤ)) ⊆ T.lang v ∧ 1 ≤ T.cut v ∧
    0 ≤ T.rad v) ∧
  (∀ v n, v ++ [n] ∈ T.verts → T.lang (v ++ [n]) ⊂ T.lang v ∧ T.rad v < T.rad (v ++ [n])) ∧
  (∀ v ∈ T.verts, ∀ M ∈ X, (T.prot v : Set (Fin d → ℤ)) ⊆ M → M ⊂ T.lang v →
    ∃ n, v ++ [n] ∈ T.verts ∧ T.lang (v ++ [n]) = M) ∧
  (∀ v ∈ T.verts, IsGeomFeasible h (fun i => T.lang (v.take i)) (fun i => q (T.lang (v.take i)))
    (fun i => T.cut (v.take i)) v.length (T.rad v))

end LocalBreadth.Supplement


