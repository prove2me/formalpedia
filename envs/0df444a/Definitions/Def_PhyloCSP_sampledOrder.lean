-- Prove2me | Definitions.Def_PhyloCSP_sampledOrder
-- name    : PhyloCSP_sampledOrder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:23:14.158368+00:00
-- url     : https://prove2.me/theorems/2b345637-6e5f-491b-930f-0e176e9374cb
-- title:
--   Conditionally independent uniform $D$-convex orders
-- statement:
--   Let $D$ be a binary tree structure on $Z$. A pair of distinct leaves represents its lowest common ancestor, two pairs representing the same branchpoint when their clusters coincide. A **uniform $D$-convex order** is sampled by choosing independently at each branchpoint, with probability $1/2$ each, which of its two child cones comes first, and comparing two leaves by the order of the child cones at their lowest common ancestor. When $D$ is random, these choices are made conditionally independently given $D$, and countably many orders $<_1,<_2,\dots$ are sampled independently.
--
--   The model: the sample space carries $D$ and an independent family of fair coins $c(j,(a,b))$. The branchpoint $x\vee_D y$ is represented by the pair $(a,b)$ of least code with $a\neq b$ and the same cluster; in the $j$-th order, $x$ precedes $y$ iff ($x$ lies in the child cone of $a$) $\iff$ ($c(j,(a,b))$ is true). Distinct branchpoints have distinct representatives, so conditional on $D$ the choices at distinct branchpoints and in distinct orders are independent fair coins.
--
--   **Formalization Note** The coins are indexed by $\mathbb N\times Z\times Z$ with the product of fair-coin measures; orders are indexed from $0$.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Section 10.1, pp.32–33 (PDF pp.34–35)

import Mathlib
import Definitions.Def_PhyloCSP_Cluster
import Definitions.Def_PhyloCSP_fraisseRel

set_option autoImplicit false

open MeasureTheory

namespace PhyloCSP

/-! # Conditionally independent uniform `D`-convex orders (Section 10.1)

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Section 10.1, pp.32–33 (PDF pp.34–35): "a pair of distinct
leaves represents their lowest common ancestor, and two pairs represent the same branchpoint if
their lowest common ancestors coincide … We sample a uniform D-convex order as follows.
Independently at each branchpoint of D, we choose which of its two child cones comes first, each
with probability 1/2. We then compare two leaves according to the order of the child cones at their
lowest common ancestor. … When D is random, we make these choices conditionally independently given
D, and we may sample countably many such orders independently."

**Formalization Note.** The sample space is `(Z → Z → Z → Bool) × (ℕ × (Z × Z) → Bool)`: the
relation `D` and an independent family of fair coins `c (j, (a, b))`. Order `j` compares distinct
`x, y` at the branchpoint `x ∨_D y`, which is represented by `repPair D x y`, the pair `(a, b)` of
least `Encodable` code with `a ≠ b` and the same cluster as `(x, y)`; coin `true` means that the
child cone of `a` comes first. Distinct branchpoints have distinct representatives, so conditional
on `D` the choices at distinct branchpoints, and in distinct orders, are independent fair coins. -/

/-- The representative pair of the branchpoint `x ∨_D y` (for `x = y`, the pair itself). -/
noncomputable def repPair (D : Z → Z → Z → Bool) (x y : Z) : Z × Z :=
  if h : x ≠ y then
    Function.argminOn (fun p : Z × Z => Encodable.encode p)
      {p : Z × Z | p.1 ≠ p.2 ∧ clusterSet D p.1 p.2 = clusterSet D x y} ⟨(x, y), h, rfl⟩
  else (x, y)

/-- The `j`-th sampled order: `x <_j y` iff `x ≠ y` and (`x` lies in the child cone of the
representative `a` of `x ∨_D y` iff the coin at `(j, (a, b))` is `true`). For `x` in the cluster of
`(a, b)`, `x` is in the cone of `a` iff `x = a` or `b` is the outgroup of `{b, x, a}`. -/
def sampledOrder (D : Z → Z → Z → Bool) (c : ℕ × (Z × Z) → Bool) (j : ℕ) (x y : Z) : Prop :=
  x ≠ y ∧ ((x = (repPair D x y).1 ∨ D (repPair D x y).2 x (repPair D x y).1 = true) ↔
    c (j, repPair D x y) = true)

/-- The fair coin on `Bool`. -/
noncomputable def fairCoin : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

/-- Independent fair coins indexed by `ℕ × (Z × Z)` (order index, representative pair). -/
noncomputable def coinMeasure : Measure (ℕ × (Z × Z) → Bool) :=
  Measure.infinitePi (fun _ : ℕ × (Z × Z) => fairCoin)

end PhyloCSP


