-- Prove2me | Definitions.Def_ChowFormsCH_comps
-- name    : ChowFormsCH_comps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:30.353731+00:00
-- url     : https://prove2.me/theorems/9b594af5-f825-4912-a108-d116098de01d
-- title:
--   Irreducible components, equidimensional sets and the $k$-equidimensional component $V_k$
-- statement:
--   For a subset $V$ of a topological space, its **irreducible components** are the maximal irreducible subsets of $V$. The **dimension** of a component $Z$ is its topological Krull dimension, the supremum of the lengths of chains of irreducible closed subsets of $Z$.
--
--   A set $V\subseteq\mathbb P^n$ is **equidimensional of dimension $k$** if all of its irreducible components have dimension $k$; the empty set qualifies for every $k$. The **$k$-equidimensional component** of $V$ is
--   $$
--   V_k=\bigcup\{Z : Z \text{ an irreducible component of } V,\ \dim Z=k\},
--   $$
--   possibly empty, so that $V=V_0\cup V_1\cup\dots\cup V_n$ for a projective variety $V\subseteq\mathbb P^n$.
--
--   The Chow forms $C_{V_0},\dots,C_{V_n}$ of these components are the outputs of Theorem 4.9.
--
--   **Formalization Note** In `ProjSpace n K` (the punctured cone) the topological dimension of a component is its projective dimension plus one, so `IsProjEquidim V k` and `equidimComponent V k` use dimension $k+1$. In affine space the topological dimension is the usual dimension (`IsPureDim V m`).
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), §1.1, p.4; §2.1, p.8; proof of Theorem 4.9, p.34

import Mathlib
import Definitions.Def_ChowFormsCH_ProjSpace

set_option autoImplicit false

namespace ChowFormsCH

/-- The irreducible components of a subset `V` of a topological space: the maximal irreducible
subsets of `V` (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH via
Chow forms*, arXiv:2611.05289, held version, sha256 75e796c6…, §2.1, p.8, "irreducible components
of V"; §1.1, p.4).

**Formalization Note** For a closed `V` (a variety) the maximal irreducible subsets are closed and
are the usual irreducible components. The dimension of a component `Z` is the topological Krull
dimension `topologicalKrullDim Z` of `Z` with the subspace topology: the supremum of lengths of
chains of irreducible closed subsets. In `K^σ` it is the usual dimension; in `ProjSpace n K` (the
punctured cone) it is the projective dimension plus one. -/
def comps {X : Type*} [TopologicalSpace X] (V : Set X) : Set (Set X) :=
  {Z | Z ⊆ V ∧ IsIrreducible Z ∧ ∀ Z' : Set X, Z' ⊆ V → IsIrreducible Z' → Z ⊆ Z' → Z' = Z}

/-- `V` is equidimensional of (topological) dimension `e`: every irreducible component of `V`
has topological Krull dimension `e`. The empty set qualifies for every `e`. -/
def IsPureDim {X : Type*} [TopologicalSpace X] (V : Set X) (e : ℕ) : Prop :=
  ∀ Z ∈ comps V, topologicalKrullDim Z = (e : WithBot ℕ∞)

/-- The union of the irreducible components of `V` of topological dimension `e` (empty if there
are none). -/
def pureDimPart {X : Type*} [TopologicalSpace X] (V : Set X) (e : ℕ) : Set X :=
  ⋃₀ {Z | Z ∈ comps V ∧ topologicalKrullDim Z = (e : WithBot ℕ∞)}

/-- A subset of `P^n` is equidimensional of projective dimension `k` (codimension `n − k`):
every irreducible component has dimension `k`, i.e. its punctured cone has topological dimension
`k + 1` (§3.1, p.22; §4.1, p.29). The empty variety is equidimensional of every dimension, as in
the paper, where an empty `V_k` has Chow form `1` (proof of Theorem 4.9, p.34). -/
def IsProjEquidim {n : ℕ} {K : Type*} [Field K] (V : Set (ProjSpace n K)) (k : ℕ) : Prop :=
  IsPureDim V (k + 1)

/-- The `k`-equidimensional component `V_k` of `V ⊆ P^n`: the union of the `k`-dimensional
irreducible components of `V`, possibly empty (§1.1, p.4: "For 0 ≤ k ≤ n, denote by V_k the
k-equidimensional component of V"). -/
def equidimComponent {n : ℕ} {K : Type*} [Field K] (V : Set (ProjSpace n K)) (k : ℕ) :
    Set (ProjSpace n K) :=
  pureDimPart V (k + 1)

end ChowFormsCH


