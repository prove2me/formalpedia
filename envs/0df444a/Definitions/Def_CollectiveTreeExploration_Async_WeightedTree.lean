-- Prove2me | Definitions.Def_CollectiveTreeExploration_Async_WeightedTree
-- name    : CollectiveTreeExploration_Async_WeightedTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:03:14.969919+00:00
-- url     : https://prove2.me/theorems/c50716eb-2b1a-4ecf-93c7-d13be392acf5
-- title:
--   Finite rooted weighted trees, transport distance, configurations and the invariant (I)
-- statement:
--   This file fixes the weighted trees of Section 2 and the operations of the tree-mining game.
--
--   **Trees.** A dynamic presentation of a weighted rooted tree has a finite vertex set (labelled by natural numbers), a root $r$, a parent map $u\mapsto p_u$ and edge lengths $d_u$ for the edge $(p_u,u)$, $u\ne r$. We write $u\preceq v$ when $u$ is a descendant of $v$ (equality allowed), $C_v$ for the children of $v$, $L$ for the set of leaves and $L_u=\{\ell\in L:\ell\preceq u\}$. For $a\preceq b$, the path $a\to b$ consists of the vertices from $a$ (included) up to $b$ (excluded), and $d(a,b)=\sum_{u\in a\to b}d_u$. A tree has depth at most $D$ when $d(v,r)\le D$ for every vertex $v$. A **game tree** satisfies the standing assumptions of the tree-mining game: every non-root edge has positive length and every non-root internal vertex has at least two children.
--
--   **Masses and transport.** For a mass function $y$ on the vertices, $y_u=\sum_{v\preceq u}y_v$ is the mass at or below $u$. The **optimal transportation distance** is
--   $$\mathrm{OT}_d(y,y')=\sum_{u\ne r}d_u\,|y_u-y'_u|.$$
--
--   **Configurations.** A **fractional configuration** of mass $k$ is $y\ge0$, supported on the leaves, with $\sum_{\ell\in L}y_\ell=k$ (zero coordinates allowed). An **integral configuration** of $k$ miners is $x$ supported on the leaves with $x_\ell\in\{1,\dots,k\}$ at every leaf and $\sum_\ell x_\ell=k$. The **invariant (I)** for $(x,y)$ is: at every leaf, $y_\ell\ge\frac12$, $x_\ell\ge1$ and $x_\ell<y_\ell+\frac32$.
--
--   **Operations.** *Elongation* changes the length $d_l$ of a leaf edge. *Fork* of a leaf $l$ into $m$ children adds $m$ fresh vertices below $l$, each with edge length $\delta$. *Deletion* of a leaf $l$ removes it; if its parent $p\ne r$ is left with a single child $c$, then $p$ is suppressed: the edges $(p_p,p)$ and $(p,c)$ are replaced by one edge $(p_p,c)$ of length $d_p+d_c$. Surviving vertices keep their labels.
--
--   **Formalization Note** The general positive finite rooted-tree object is the published `PolylogKServer.HST.WTree`, referenced separately. A raw dynamic record (vertex `Finset`, root, parent map, lengths) permits forks, deletion and limiting zero lengths. Its validity requires a published tree on the live vertex subtype with exactly the same root, parent and positive edge lengths. The published depth field is the number of parent steps and adds no geometric assumption; no HST or weighted-HST predicate is used. Mass functions are functions on all labels; masses on internal vertices are only used to compare the configuration before a fork (miners on the forked vertex) with the one after.
-- source:
--   Romain Cosson, Laurent Massoulié, Polylogarithmic Collective Tree Exploration, STOC 2027 submission #263 (October 2026), source.pdf sha256 54f5e43ddf9269e11a2fff4aa4b0ea62348afe16a38aba551313f43cbf3e00e0; §2.1, p.5 (notation, configurations, transportation); §2.2, p.6 (operations and standing assumptions); invariant (I), Proposition 3.2, p.7

import Mathlib
import Definitions.Def_PolylogKServer_HST_Tree

namespace CollectiveTreeExploration.Async

open scoped BigOperators

noncomputable section

open Classical

/-! # Finite rooted weighted trees (Cosson–Massoulié, STOC 2027 #263, §2.1, p.5; §2.2, p.6)

Vertices are natural-number labels, so that a tree can grow (forks add fresh labels) and shrink
(deletions remove labels) while every surviving vertex keeps its label. A tree is the data of a
finite vertex set, a root, a parent map and edge lengths; validation uses the published positive finite rooted-tree type
`PolylogKServer.HST.WTree`. The raw record also represents limiting zero-length data. -/

/-- A weighted rooted tree on natural-number labels: vertex set `V`, root `root`, parent map
`par` (with `par root = root`) and edge lengths `len u = d_u`, the length of the edge
`(p_u, u)`. The value `len root` is never used. -/
structure WTree where
  V : Finset ℕ
  root : ℕ
  par : ℕ → ℕ
  len : ℕ → ℝ

namespace WTree

variable (T : WTree)

/-- The published static positive tree represents this dynamic presentation, preserving
its root, parent map and every actual edge length. Its depth witness is only the number
of parent steps, not a geometric restriction or an HST assumption. -/
def Represents (B : PolylogKServer.HST.WTree {v // v ∈ T.V}) : Prop :=
  B.root.val = T.root ∧ (∀ v, (B.parent v).val = T.par v.val) ∧
    ∀ v, v.val ≠ T.root → B.W v = T.len v.val

/-- `u ⪯ v`: `u` is a descendant of `v`, equality allowed (p.5). -/
def Desc (u v : ℕ) : Prop := ∃ n : ℕ, T.par^[n] u = v

/-- The children `C_v` of `v`. -/
def children (v : ℕ) : Finset ℕ := T.V.filter (fun w => w ≠ v ∧ T.par w = v)

/-- The leaves `L(T)`: vertices without children. (The root is a leaf exactly when it is the
only vertex.) -/
def leaves : Finset ℕ := T.V.filter (fun v => T.children v = ∅)

/-- `L_u = {ℓ ∈ L : ℓ ⪯ u}`. -/
def leavesBelow (u : ℕ) : Finset ℕ := T.leaves.filter (fun ℓ => T.Desc ℓ u)

/-- The vertices of the path `a → b` for `a ⪯ b`: it includes `a` and excludes `b` (p.5). -/
def pathVerts (a b : ℕ) : Finset ℕ := T.V.filter (fun u => T.Desc a u ∧ T.Desc u b ∧ u ≠ b)

/-- `d(a, b) = ∑_{u ∈ a → b} d_u`, the length of the path from `a` up to its ancestor `b`. -/
def dist (a b : ℕ) : ℝ := ∑ u ∈ T.pathVerts a b, T.len u

/-- Weighted depth of a vertex: `d(v, r)`. -/
def distRoot (v : ℕ) : ℝ := T.dist v T.root

/-- The tree has depth at most `D`: every vertex (equivalently every leaf) is at distance at most
`D` from the root, `max_{ℓ ∈ L} d(r, ℓ) ≤ D` (p.5). -/
def DepthLE (D : ℝ) : Prop := ∀ v ∈ T.V, T.distRoot v ≤ D

/-- The standing assumptions on the trees of the continuous tree-mining game (§2.2, p.6):
a tree, positive length on every existing non-root edge, and every non-root internal vertex has
at least two children. -/
structure IsGameTree : Prop where
  positiveTree : ∃ B : PolylogKServer.HST.WTree {v // v ∈ T.V}, T.Represents B
  branching : ∀ v ∈ T.V, v ≠ T.root → v ∉ T.leaves → 2 ≤ (T.children v).card

/-! ## Masses, transport and configurations (p.5) -/

/-- The mass `y_u = ∑_{v ⪯ u} y_v` at or below `u` of a vertex-mass function `y`. For a
configuration supported on leaves this is `∑_{ℓ ∈ L_u} y_ℓ`. Allowing mass on internal vertices
is used only to compare a configuration before a fork (mass on the forked vertex) with one after. -/
def mass (y : ℕ → ℝ) (u : ℕ) : ℝ := ∑ v ∈ T.V.filter (fun v => T.Desc v u), y v

/-- The real-valued version of an integral configuration. -/
def toReal (x : ℕ → ℕ) : ℕ → ℝ := fun v => (x v : ℝ)

/-- The optimal transportation distance `OT_d(y, y') = ∑_{u ≠ r} d_u |y_u - y'_u|` (p.5). -/
def OT (y y' : ℕ → ℝ) : ℝ :=
  ∑ u ∈ T.V.erase T.root, T.len u * |T.mass y u - T.mass y' u|

/-- A fractional configuration with total mass `k`: nonnegative, supported on the leaves,
`∑_{ℓ ∈ L} y_ℓ = k` (p.5). Zero leaf coordinates are allowed. -/
def IsFracConfig (k : ℕ) (y : ℕ → ℝ) : Prop :=
  (∀ v, v ∉ T.leaves → y v = 0) ∧ (∀ v, 0 ≤ y v) ∧ ∑ ℓ ∈ T.leaves, y ℓ = (k : ℝ)

/-- An integral configuration of `k` miners: supported on the leaves, `x_ℓ ∈ {1, …, k}` at every
leaf, `∑_{ℓ ∈ L} x_ℓ = k` (p.5). -/
def IsIntConfig (k : ℕ) (x : ℕ → ℕ) : Prop :=
  (∀ v, v ∉ T.leaves → x v = 0) ∧ (∀ ℓ ∈ T.leaves, 1 ≤ x ℓ) ∧ ∑ ℓ ∈ T.leaves, x ℓ = k

/-- The invariant (I) of Proposition 3.2 (p.7) for an integral configuration `x` and a fractional
configuration `y`: at every leaf `y_ℓ ≥ 1/2`, `x_ℓ ≥ 1`, and `x_ℓ < y_ℓ + 3/2`. -/
def InvI (x : ℕ → ℕ) (y : ℕ → ℝ) : Prop :=
  ∀ ℓ ∈ T.leaves, (1 / 2 : ℝ) ≤ y ℓ ∧ 1 ≤ x ℓ ∧ (x ℓ : ℝ) < y ℓ + 3 / 2

/-! ## Tree operations of the tree-mining game (§2.2, p.6) -/

/-- The tree with the length of the edge `(p_l, l)` set to `L` (an elongation of `l` by
`L - d_l`). -/
def setLen (l : ℕ) (L : ℝ) : WTree := { T with len := Function.update T.len l L }

/-- First unused label: one more than the largest vertex label. -/
def fresh : ℕ := T.V.sup id + 1

/-- The labels `fresh, …, fresh + m - 1` given to the `m` children created by a fork. -/
def forkLabels (m : ℕ) : Finset ℕ := (Finset.range m).image (fun i => T.fresh + i)

/-- Fork of the leaf `l` into `m` new children, all with edge length `δ`. -/
def fork (l m : ℕ) (δ : ℝ) : WTree where
  V := T.V ∪ T.forkLabels m
  root := T.root
  par := fun w => if T.fresh ≤ w ∧ w < T.fresh + m then l else T.par w
  len := fun w => if T.fresh ≤ w ∧ w < T.fresh + m then δ else T.len w

/-- Deletion of the leaf `l`, followed by suppression of its parent `p = p_l` when `p` is not the
root and is left with a single child `c`: the two edges `(p_p, p)` and `(p, c)` are replaced by one
edge `(p_p, c)` of length `d_p + d_c` (p.6). The surviving vertices keep their labels. -/
def delete (l : ℕ) : WTree :=
  let p := T.par l
  let rest := (T.children p).erase l
  if h : p ≠ T.root ∧ rest.card = 1 then
    let c := (Finset.card_eq_one.mp h.2).choose
    { V := (T.V.erase l).erase p
      root := T.root
      par := fun w => if w = c then T.par p else T.par w
      len := fun w => if w = c then T.len c + T.len p else T.len w }
  else
    { T with V := T.V.erase l }

end WTree

end

end CollectiveTreeExploration.Async


