-- Prove2me | Definitions.Def_PhyloCSP_rawOut
-- name    : PhyloCSP_rawOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:22:57.304387+00:00
-- url     : https://prove2.me/theorems/aa503ee9-227e-4f64-94c5-8b2b19aae21a
-- title:
--   The output relation of a basic transformation for fixed random choices
-- statement:
--   Fix a template $B$, an input tree with rooted-triplet relation $C$ on a finite linearly ordered leaf set $X$, an assignment $\xi:X\to\mathrm{Loc}(B)$ of leaves to locations (step 1 of Definition 3.3), and sign vectors $r(v)\in\{\pm1\}^{E(B)}$ at the internal nodes $v$ of the input (step 3). Steps 2–4 then produce a deterministic output tree; this definition gives its rooted-triplet relation. The output has the following clusters (leaf sets below vertices):
--
--   1. for every template vertex $w$, the set $\mathrm{Below}(w)$ of leaves assigned to template leaves at or below $w$ or to edges into strict descendants of $w$;
--   2. for every template edge $e$ into $w$, with assigned leaves $x_1,\dots,x_m$ listed in the caterpillar order (Definition 1.6) given by the coordinates $r_e(v)$, the sets $\{x_i,\dots,x_m\}\cup\mathrm{Below}(w)$: leaf $x_i$ hangs at the $i$-th new node from the endpoint closer to the root;
--   3. for every template leaf $u$, the clusters of the induced input tree $T{\restriction}S_u$, attached at $u$.
--
--   Then $x\mid yz$ holds in the output iff $x,y,z$ are distinct and some cluster contains $y,z$ but not $x$. Clusters of type 3 separate only leaves of one set $S_u$, so they are represented by the input triplets among the leaves of $S_u$.
--
--   In the caterpillar order, the two children of each internal node $v$ of the input are labeled $\pm1$, and the child labeled $r_e(v)$ comes first; $x$ precedes $y$ according to the label of the child of $x\vee y$ containing $x$.
--
--   **Formalization Note** Definition 1.6 labels children arbitrarily; here the child containing the least leaf of the cluster is labeled $+1$ (true). The paper observes (p.8) that the output law does not depend on this choice because the orientation law is centrally symmetric. Internal nodes of the input are its clusters of size at least two. The deletion of unused template parts and the suppression of unary nodes (step 4) do not change these triplets. The description reproduces Figure 2 of the paper (checked by computation).
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Definition 1.6, p.4 (PDF p.6); Definition 3.3, p.8 (PDF p.10); Figure 2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_PhyloCSP_Cluster
import Definitions.Def_PhyloCSP_Template

set_option autoImplicit false

namespace PhyloCSP

open Template

/-! # The deterministic output of a basic transformation (Definition 3.3, steps 2–4)

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Definition 1.6, p.4 (PDF p.6) and Definition 3.3, p.8
(PDF p.10).

**Formalization Note.** The output is described by its rooted-triplet relation, computed from the
clusters (leaf sets below vertices) of the tree built in steps 2–3, which step 4 (deleting unused
parts, suppressing unary nodes) does not change:
(a) `Below w`: the leaves assigned to template leaves at or below the template vertex `w`, or to
    edges into strict descendants of `w`;
(b) for an edge `e` into `w` with assigned leaves `x₁, …, x_m` in caterpillar order, the sets
    `{xᵢ, …, x_m} ∪ Below w` (leaf `xᵢ` hangs at the `i`-th new node from the top);
(c) at a template leaf `u`, the clusters of the induced input tree `T↾S_u`, which separate only
    leaves of `S_u` and are represented by the input triplets among `S_u`.
Internal nodes of the input are its clusters `clusterOf C a b` (`a ≠ b`). Definition 1.6 labels the
two children of each internal node arbitrarily by `±1`; here the child containing the least leaf
of the cluster is labeled `+1` (`true`). The paper notes (p.8) that the law does not depend on this
choice because `ν` is centrally symmetric. A child labeled `r(v)` is drawn on the left, i.e. comes
first. -/

variable {X : Type} [Fintype X] [LinearOrder X]

/-- The internal nodes of an input tree relation `C` on a finite leaf type: its clusters with at
least two leaves. -/
abbrev IntNode (C : X → X → X → Bool) : Type :=
  {K : Finset X // ∃ a b, a ≠ b ∧ K = clusterOf C a b}

/-- `x` lies in the child (of the internal node `x ∨ y`) that contains the least leaf of the
cluster: that child is labeled `+1`. -/
def OnMinSide (C : X → X → X → Bool) (x y : X) : Prop :=
  x = (clusterOf C x y).min' ⟨x, mem_clusterOf_left C x y⟩ ∨
    (y ≠ (clusterOf C x y).min' ⟨x, mem_clusterOf_left C x y⟩ ∧
      C y x ((clusterOf C x y).min' ⟨x, mem_clusterOf_left C x y⟩) = true)

instance (C : X → X → X → Bool) (x y : X) : Decidable (OnMinSide C x y) := by
  unfold OnMinSide; infer_instance

/-- The caterpillar order of Definition 1.6 specified by signs `s` at the internal nodes: `x`
comes strictly before `y` iff, at `v = x ∨ y`, `x` lies in the child labeled `s(v)` (drawn on
the left). -/
def CatBefore (C : X → X → X → Bool) (s : IntNode C → Bool) (x y : X) : Prop :=
  ∃ h : x ≠ y, (OnMinSide C x y ↔ s ⟨clusterOf C x y, x, y, h, rfl⟩ = true)

instance (C : X → X → X → Bool) (s : IntNode C → Bool) (x y : X) :
    Decidable (CatBefore C s x y) := by
  unfold CatBefore; infer_instance

/-- Whether a location lies below the template vertex `w`: a template leaf at or below `w`, or the
edge into a strict descendant of `w`. -/
def locBelow (B : Template) (w : Fin B.n) : B.Loc → Bool :=
  Sum.elim (fun u => decide (B.AtOrBelow w u.1)) (fun e => decide (e.1 ≠ w ∧ B.AtOrBelow w e.1))

/-- (a) The leaves below the template vertex `w`. -/
def Below (B : Template) (ξ : X → B.Loc) (w : Fin B.n) : Finset X :=
  Finset.univ.filter (fun x => locBelow B w (ξ x) = true)

/-- (b) The leaves at or after `x` along the edge `e` (in the caterpillar order with the
coordinates `r(·)_e` of the signs), together with everything below the lower endpoint of `e`. -/
def edgeSuffix (B : Template) (C : X → X → X → Bool) (ξ : X → B.Loc)
    (r : IntNode C → B.Edge → Bool) (e : B.Edge) (x : X) : Finset X :=
  Finset.univ.filter (fun y => ξ y = Sum.inr e ∧ (y = x ∨ CatBefore C (fun v => r v e) x y)) ∪
    Below B ξ e.1

/-- **The output relation** of a basic transformation with template `B` on the input relation
`C`, for the location assignment `ξ` (step 1) and the sign vectors `r(v) ∈ {±1}^{E(B)}` at the
internal nodes `v` of the input (step 3): `x | yz` in the output iff `x, y, z` are distinct and
some output cluster contains `y, z` but not `x`. -/
def rawOut (B : Template) (C : X → X → X → Bool) (ξ : X → B.Loc)
    (r : IntNode C → B.Edge → Bool) (x y z : X) : Prop :=
  x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    ((∃ w : Fin B.n, y ∈ Below B ξ w ∧ z ∈ Below B ξ w ∧ x ∉ Below B ξ w) ∨
      (∃ (e : B.Edge) (x' : X), ξ x' = Sum.inr e ∧ y ∈ edgeSuffix B C ξ r e x' ∧
        z ∈ edgeSuffix B C ξ r e x' ∧ x ∉ edgeSuffix B C ξ r e x') ∨
      (∃ u : B.Leaf, ξ x = Sum.inl u ∧ ξ y = Sum.inl u ∧ ξ z = Sum.inl u ∧ C x y z = true))

instance (B : Template) (C : X → X → X → Bool) (ξ : X → B.Loc)
    (r : IntNode C → B.Edge → Bool) (x y z : X) : Decidable (rawOut B C ξ r x y z) := by
  unfold rawOut; infer_instance

end PhyloCSP


