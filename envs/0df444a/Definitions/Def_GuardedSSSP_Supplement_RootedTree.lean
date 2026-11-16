-- Prove2me | Definitions.Def_GuardedSSSP_Supplement_RootedTree
-- name    : GuardedSSSP_Supplement_RootedTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:19:24.674331+00:00
-- url     : https://prove2.me/theorems/675d0446-6964-4f43-9822-e08bcf4f830c
-- title:
--   Rooted trees, ancestors, leaves, dominator trees, single-entry trees (Definition D.1) and child-before-parent orders
-- statement:
--   Let $V=\{0,\dots,n-1\}$.
--
--   1. A **rooted tree** on $V$ with root $r$ is a parent map $\mathrm{par}:V\to V$ with $\mathrm{par}(r)=r$ such that every vertex reaches $r$ by iterating $\mathrm{par}$. We write $a\preceq u$ ($a$ is an ancestor of $u$, equality included) when $a=\mathrm{par}^k(u)$ for some $k\ge0$. A **child** of $g$ is a vertex $a\ne r$ with $\mathrm{par}(a)=g$, and a **leaf** is a vertex without children; $h$ denotes the number of leaves.
--   2. For a flow graph $(H,r)$, a vertex $g$ **dominates** $v$ if every walk from $r$ to $v$ visits $g$ (the base mission's domination). The **immediate dominator** of $v\ne r$ is the strict dominator of $v$ that is dominated by every strict dominator of $v$, and the **dominator tree** is the rooted tree $v\mapsto\mathrm{idom}(v)$, $r\mapsto r$.
--   3. (Definition D.1) A rooted tree $D$ on $V$ with root $r$ is **single-entry** for $H$ if every nonloop arc $(u,v)$ satisfies either $v\preceq u$, or $v\ne r$ and $\mathrm{par}_D(v)\preceq u$. The tree need not be a subgraph of $H$.
--   4. A **child-before-parent order** is a bijection $\mathrm{ord}:V\to\{0,\dots,n-1\}$ of positions in which every non-root vertex precedes its parent.
--
--   These objects describe the parameter $h$ of Theorem C.1, the trees for which Theorem E.3 holds, and the inputs of Theorem F.1.
--
--   **Formalization Note** The condition $\mathrm{par}(r)=r$ is a convention for the root's parent slot; reaching $r$ from every vertex rules out cycles. With $n=1$ the root is the only vertex and the only leaf.
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), Theorem C.1, p.37 (PDF p.38); Appendix D and Definition D.1, p.38 (PDF p.39); Lemma D.2; Appendix E.1, p.39 (PDF p.40); Theorem F.1, p.41 (PDF p.42)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network
import Definitions.Def_GuardedSSSP_Dominates

namespace GuardedSSSP

namespace Supplement

open AtomicDynRouting.ResidenceTime

/-!
# Rooted trees, dominator trees, single-entry trees and child-before-parent orders

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…).

* Theorem C.1, p.37 (PDF p.38): "Choose a root r reaching every vertex, and let its dominator tree have
  h leaves."
* Appendix D, p.38 (PDF p.39): "For a rooted tree D, write D_a for the subtree at a and a ⪯ u when a is
  an ancestor of u, including equality. For a ⪯ u, let D[a, u] be the set of vertices on the tree path from
  a to u, and put D(a, u] = D[a, u] ∖ {a}. The tree itself need not be a subgraph of H."
* Definition D.1, p.38 (PDF p.39): "A rooted tree D on V, with root r, is single-entry for H if every
  nonloop arc (u, v) satisfies either v ⪯ u, or v ≠ r and parent_D(v) ⪯ u."
* Appendix E.1, p.39 (PDF p.40), and Theorem F.1, p.41 (PDF p.42): "child-before-parent" orders and
  sequences.

**Formalization Note.**
* A rooted tree on `Fin n` with root `r` is a parent function `par : Fin n → Fin n` with `par r = r`
  (the root's parent slot points to itself) such that every vertex reaches `r` by iterating `par`. This
  forces acyclicity: a non-root vertex is never its own iterated parent.
* `IsAnc par a u` (`a ⪯ u`) holds when `a = par^[k] u` for some `k ≥ 0`, so it includes equality.
* A child of `g` is a vertex `a ≠ r` with `par a = g`; a leaf is a vertex with no child. For `n = 1` the
  root is the only vertex and the only leaf.
* Domination is the base mission's `GuardedSSSP.Dominates` (every walk from the root visits the vertex).
  `idom v` (for `v ≠ r`) is the strict dominator of `v` dominated by every strict dominator of `v`; the
  dominator tree is the parent function `v ↦ idom v`, with `r ↦ r`.
* A child-before-parent order is a position bijection `ord : Fin n ≃ Fin n` in which every non-root
  vertex comes before its parent.
-/

/-- `par` is a rooted tree on `Fin n` with root `r`: `par r = r` and every vertex reaches `r` by
iterating `par`. -/
def IsRootedTree {n : ℕ} (par : Fin n → Fin n) (r : Fin n) : Prop :=
  par r = r ∧ ∀ v : Fin n, ∃ k : ℕ, par^[k] v = r

/-- `a ⪯ u`: `a` is an ancestor of `u` in the tree `par`, equality included. -/
def IsAnc {n : ℕ} (par : Fin n → Fin n) (a u : Fin n) : Prop :=
  ∃ k : ℕ, par^[k] u = a

/-- `a` is a child of `g` in the tree `par` with root `r`. -/
def IsChild {n : ℕ} (par : Fin n → Fin n) (r g a : Fin n) : Prop :=
  a ≠ r ∧ par a = g

open Classical in
/-- The number `h` of leaves (vertices without a child) of the tree `par` with root `r`. -/
noncomputable def numLeaves {n : ℕ} (par : Fin n → Fin n) (r : Fin n) : ℕ :=
  (Finset.univ.filter (fun v : Fin n => ∀ u : Fin n, ¬ IsChild par r v u)).card

/-- `g` is the immediate dominator of `v ≠ g` with respect to the root `r`: `g` strictly dominates `v`
and every strict dominator of `v` dominates `g`. -/
def IsImmDom {n m : ℕ} (G : Network (Fin n) (Fin m)) (r g v : Fin n) : Prop :=
  g ≠ v ∧ Dominates G r g v ∧ ∀ g' : Fin n, g' ≠ v → Dominates G r g' v → Dominates G r g' g

/-- `dpar` is the dominator tree of the flow graph `(G, r)`: `dpar r = r` and `dpar v = idom v` for
every `v ≠ r`. -/
def IsDomTree {n m : ℕ} (G : Network (Fin n) (Fin m)) (r : Fin n) (dpar : Fin n → Fin n) : Prop :=
  dpar r = r ∧ ∀ v : Fin n, v ≠ r → IsImmDom G r (dpar v) v

/-- Definition D.1: the rooted tree `par` (root `r`) is single-entry for `G`: every nonloop arc `(u, v)`
has `v ⪯ u`, or `v ≠ r` and `par v ⪯ u`. -/
def IsSingleEntry {n m : ℕ} (G : Network (Fin n) (Fin m)) (par : Fin n → Fin n) (r : Fin n) : Prop :=
  ∀ e : Fin m, G.tail e ≠ G.head e →
    IsAnc par (G.head e) (G.tail e) ∨ (G.head e ≠ r ∧ IsAnc par (par (G.head e)) (G.tail e))

/-- `ord` is a child-before-parent order of the tree `par` (root `r`): every non-root vertex has a
smaller position than its parent. -/
def IsChildBeforeParent {n : ℕ} (par : Fin n → Fin n) (r : Fin n) (ord : Fin n ≃ Fin n) : Prop :=
  ∀ v : Fin n, v ≠ r → ord v < ord (par v)

end Supplement

end GuardedSSSP


