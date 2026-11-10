-- Prove2me | Definitions.Def_SetDefinedGraphs_VectorSets
-- name    : SetDefinedGraphs_VectorSets
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:24:48.880581+00:00
-- url     : https://prove2.me/theorems/61ec71dd-31df-4a0e-9fee-0c1916309877
-- title:
--   Injective, order-uniform and $P$-homogeneous sets of vectors; restrictions and slices $V_{L,a}$
-- statement:
--   Vectors are functions $v:I\to\mathbb N$ on a coordinate set $I$ ($I=[d]$ gives $\mathbb N^d$).
--
--   1. $V$ is **injective**, $V\subseteq\mathbb N^{\underline d}$, if every $v\in V$ is an injective function.
--   2. $u,w$ have the **same order type** if $u_i<u_j\iff w_i<w_j$ for all $i,j$; $V$ is **order-uniform** if all its elements have the same order type.
--   3. For $S\subseteq I$, $v|_S$ is the restriction of $v$ to $S$ and $V|_S=\{v|_S:v\in V\}$.
--   4. For a partition $P$ of the coordinates, $v$ is **$P$-homogeneous** if $v_i=v_j\iff i$ and $j$ lie in the same $P$-class; $V$ is $P$-homogeneous if all its elements are.
--   5. For $L\subseteq[d]$ and $a\in\mathbb N^L$, the **slice** is $V_{L,a}=\{v\in V: v|_L=a\}$.
--
--   **Formalization Note** A partition of $[d]$ is encoded by its equivalence relation (a `Setoid`), whose classes are the $P$-classes.
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), §3 Preliminaries p.14 (PDF p.16): ℕ^I, ℕ^I̲, v|S, V|S, order type, order-uniform, injective; §4.2 p.25 (P-homogeneous); §4.3.2 p.28 (V_{L,a})

import Mathlib

set_option autoImplicit false

namespace SetDefinedGraphs

/-- A set `V ⊆ ℕ^ι` is **injective** if every vector in it is an injective function, `V ⊆ ℕ^ι̲`
(arXiv:2607.23754, §3 Preliminaries, p.14). -/
def IsInjectiveSet {ι : Type} (V : Set (ι → ℕ)) : Prop :=
  ∀ v ∈ V, Function.Injective v

/-- Two vectors `u, w ∈ ℕ^ι` have the **same order type** if `u_i < u_j ⇔ w_i < w_j` for all `i, j`
(arXiv:2607.23754, p.14). -/
def SameOrderType {ι : Type} (u w : ι → ℕ) : Prop :=
  ∀ i j, u i < u j ↔ w i < w j

/-- A set `V ⊆ ℕ^ι` is **order-uniform** if all its elements have the same order type (arXiv:2607.23754, p.14). -/
def IsOrderUniform {ι : Type} (V : Set (ι → ℕ)) : Prop :=
  ∀ u ∈ V, ∀ w ∈ V, SameOrderType u w

/-- The restriction `v|_I` of a vector `v ∈ ℕ^ι` to the coordinates in `I` (arXiv:2607.23754, p.14). -/
def restrictVec {ι : Type} (I : Set ι) (v : ι → ℕ) : I → ℕ :=
  fun i => v i.1

/-- The restriction `V|_I := {v|_I : v ∈ V}` of a set of vectors to the coordinates in `I` (arXiv:2607.23754, p.14). -/
def restrictSet {ι : Type} (I : Set ι) (V : Set (ι → ℕ)) : Set (I → ℕ) :=
  (fun v => restrictVec I v) '' V

/-- For a partition `P` of the coordinates, a vector `v` is **`P`-homogeneous** if `v_i = v_j ⇔ i` and `j` are in the
same `P`-class (arXiv:2607.23754, §4.2, p.25).

**Formalization Note** A partition of `[d]` is encoded by its equivalence relation (`Setoid`); its classes are the
`P`-classes. -/
def IsPHomogeneousVec {ι : Type} (P : Setoid ι) (v : ι → ℕ) : Prop :=
  ∀ i j, v i = v j ↔ P.r i j

/-- A set `V` is **`P`-homogeneous** if every `v ∈ V` is `P`-homogeneous (arXiv:2607.23754, p.25). -/
def IsPHomogeneous {ι : Type} (P : Setoid ι) (V : Set (ι → ℕ)) : Prop :=
  ∀ v ∈ V, IsPHomogeneousVec P v

/-- For `L ⊆ [d]` and `a ∈ ℕ^L`, the slice `V_{L,a} := {v ∈ V : v|_L = a}` (arXiv:2607.23754, §4.3.2, p.28). -/
def sliceSet {d : ℕ} (V : Set (Fin d → ℕ)) (L : Finset (Fin d)) (a : L → ℕ) : Set (Fin d → ℕ) :=
  {v | v ∈ V ∧ ∀ i : L, v i.1 = a i}

end SetDefinedGraphs


