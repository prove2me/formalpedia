-- Prove2me | Definitions.Def_RamseyLST_Main_HST
-- name    : RamseyLST_Main_HST
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:07:24.009058+00:00
-- url     : https://prove2.me/theorems/54831669-5813-47a6-916e-74f09dcb9c3c
-- title:
--   Ultrametrics as labelled trees, and $\mu$-HSTs (Definition 4)
-- statement:
--   An **ultrametric** (Definition 4) is a finite metric space whose points are the leaves of a rooted tree in which every node $u$ has a label $\delta(u)\ge0$, labels do not increase from a node to its descendants, and $\delta(u)=0$ exactly when $u$ is a leaf. The distance between leaves $x,y$ is
--
--   $$d(x,y)=\delta(\operatorname{lca}(x,y)),$$
--
--   the label of their least common ancestor. It is a **$\mu$-HST** if $\delta(u)\ge\mu\,\delta(v)$ whenever $u$ is the parent of $v$; a 1-HST, i.e. any such ultrametric, is called an **HST**.
--
--   Here each node is recorded by its set of descendant leaves: the nodes form a laminar family of non-empty subsets of the point set $P$ that contains $P$ itself (the root) and every singleton $\{x\}$ (the leaves). Two nodes are nested or disjoint. The least common ancestor of $x,y$ is the smallest node containing both, and the parent of a node $S$ is the smallest node strictly containing $S$.
--
--   These trees are the targets of Theorem 5 and Lemmas 6–7.
--
--   **Formalization Note** The distance is the minimum label over the nodes containing both points, which is the label of the least common ancestor because labels are monotone along the chain of nodes containing a point. Unary nodes (a node with a single child) are not representable: they do not change the metric, and removing one preserves the $\mu$-HST property for $\mu\ge1$.
-- source:
--   Bartal, Hovav, Nearly Tight Low-Stretch Ramsey Spanning Trees, STOC 2027 submission (manuscript sha256 bcaed0afb9db0cccb453599c9f6915e958922563d3989766c4affc99a15de44d), p. 10 (PDF 14), Definition 4

import Mathlib

namespace RamseyLST.Main

/-- Definition 4 (p. 10): an ultrametric given by a finite rooted labelled tree whose leaves are
the points of `P`. Each node of the tree is recorded by its set of descendant leaves: `nodes` is
a laminar family of non-empty subsets of `P` containing the root `P` itself and every leaf `{x}`.
The labels `δ` are non-increasing from a node to its descendants, and `δ(u) = 0` exactly at the
leaves. -/
structure HST (P : Type) [Fintype P] [DecidableEq P] where
  /-- The nodes, each recorded as its set of descendant leaves. -/
  nodes : Finset (Finset P)
  /-- The label `δ` of a node. -/
  label : Finset P → ℝ
  /-- The root, whose descendants are all the points. -/
  univ_mem : (Finset.univ : Finset P) ∈ nodes
  /-- Every point is a leaf. -/
  singleton_mem : ∀ x : P, ({x} : Finset P) ∈ nodes
  /-- Every node has a descendant leaf. -/
  nonempty_of_mem : ∀ S ∈ nodes, S.Nonempty
  /-- Two nodes are nested (one descends from the other) or have disjoint sets of leaves. -/
  laminar : ∀ S ∈ nodes, ∀ S' ∈ nodes, S ⊆ S' ∨ S' ⊆ S ∨ Disjoint S S'
  /-- `δ(u) = 0` if and only if `u` is a leaf. -/
  label_eq_zero_iff : ∀ S ∈ nodes, label S = 0 ↔ S.card = 1
  /-- If `v` is a descendant of `u` then `δ(u) ≥ δ(v)`. -/
  label_mono : ∀ S ∈ nodes, ∀ S' ∈ nodes, S ⊆ S' → label S ≤ label S'

namespace HST

variable {P : Type} [Fintype P] [DecidableEq P]

/-- The distance `d(x, y) = δ(lca(x, y))`: the label of the least common ancestor of the
leaves `x` and `y`, i.e. the smallest label of a node containing both (the nodes containing `x`
form a chain, and labels are monotone along it). -/
noncomputable def dist (H : HST P) (x y : P) : ℝ :=
  if h : (H.nodes.filter (fun S => x ∈ S ∧ y ∈ S)).Nonempty then
    (H.nodes.filter (fun S => x ∈ S ∧ y ∈ S)).inf' h H.label
  else 0

/-- Definition 4 (p. 10): the ultrametric is a `µ`-HST if `δ(u) ≥ µ · δ(v)` whenever `u` is the
parent of `v`, i.e. `u` is the smallest node strictly containing `v`. -/
def IsMuHST (H : HST P) (mu : ℝ) : Prop :=
  ∀ S ∈ H.nodes, ∀ S' ∈ H.nodes, S ⊂ S' → (∀ S'' ∈ H.nodes, S ⊂ S'' → S' ⊆ S'') →
    mu * H.label S ≤ H.label S'

end HST

end RamseyLST.Main


