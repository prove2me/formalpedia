-- Prove2me | Definitions.Def_MISInducedMinor_Supplement_CmlLE
-- name    : MISInducedMinor_Supplement_CmlLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:38:37.066196+00:00
-- url     : https://prove2.me/theorems/2971eb51-7c90-42af-8295-16847a6dc4dd
-- title:
--   Component max-leaf at most $k$
-- statement:
--   For a finite graph $R$, the **component max-leaf** $\mathrm{cml}(R)$ is the maximum number of leaves of a spanning tree of a connected component of $R$, where a one-vertex tree has one leaf. This item defines the predicate
--   $$\mathrm{cml}(R)\le k:\quad \text{every spanning tree of every component of } R \text{ has at most } k \text{ leaves.}$$
--
--   The **reduced component max-leaf** $\mathrm{cml}^{\downarrow}(G)$ is the least $k$ such that $G$ has a contraction sequence all of whose red graphs satisfy $\mathrm{cml}\le k$; since a vertex of degree $d$ gives a spanning tree with at least $d$ leaves, the same sequence witnesses twin-width at most $k$.
--
--   **Formalization Note** A spanning tree of the component $C$ is a tree on the vertex set of $C$ using only edges of $R$. A leaf is a vertex of degree at most one in the tree, so a one-vertex tree has one leaf. A graph with no vertices satisfies the predicate for every $k$.
-- source:
--   Bonnet, Chang, Max Independent Set Remains NP-hard when Excluding a Planar Induced Minor (and More), arXiv:2609.11285 (sha256 e378b906…), §2.2, p.5

import Mathlib

set_option autoImplicit false

namespace MISInducedMinor.Supplement

open Classical in
/-- **Component max-leaf at most `k`**: `cml(R) ≤ k`, i.e. every spanning tree of every connected
component of `R` has at most `k` leaves. Bonnet, Chang, *Max Independent Set Remains NP-hard when Excluding a Planar Induced Minor (and More)*, arXiv:2609.11285 (sha256 e378b906…), §2.2, p.5: "The component max-leaf of a graph G,
denoted by cml(G), is the maximum number of leaves in any spanning tree of any component of G. A
one-vertex tree has one leaf."

**Formalization Note.** A spanning tree of the component `C` is a graph `T` on the vertex set of
`C` (`C.supp`) that is a tree and uses only edges of `R` (`T ≤ R.induce C.supp`). A leaf is a
vertex of degree at most one in `T`, so a one-vertex tree has one leaf, as on the page. A graph
with no vertices has no component and satisfies `CmlLE R k` for every `k`. -/
def CmlLE {W : Type*} [Fintype W] (R : SimpleGraph W) (k : ℕ) : Prop :=
  ∀ (C : R.ConnectedComponent) (T : SimpleGraph C.supp), T ≤ R.induce C.supp → T.IsTree →
    Fintype.card {v : C.supp // T.degree v ≤ 1} ≤ k

end MISInducedMinor.Supplement


