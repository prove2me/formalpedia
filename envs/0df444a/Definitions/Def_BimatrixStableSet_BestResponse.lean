-- Prove2me | Definitions.Def_BimatrixStableSet_BestResponse
-- name    : BimatrixStableSet_BestResponse
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:19:07.955993+00:00
-- url     : https://prove2.me/theorems/6a928530-2888-41cf-b014-2a38810e29ac
-- title:
--   Non-degenerate games, best-response polyhedra (3), labels, equilibria (Definition 1)
-- statement:
--   This module fixes the game-theoretic objects of the paper for an $m\times n$ bimatrix game $(A,B)$. Mixed strategies and Nash equilibria are those of the published definition `RankOneBimatrix_BinSearch_Game`.
--
--   1. **Non-degeneracy** (p.5). For any mixed strategy $z$ of a player, at most $|\mathrm{supp}(z)|$ pure strategies are best responses to $z$.
--   2. **Best-response polyhedra** (display (3), p.6). They are
--
--   $$
--   P=\{x\in\mathbb R^m\mid x\ge0,\ B^\top x\le\mathbf 1\},\qquad Q=\{y\in\mathbb R^n\mid Ay\le\mathbf 1,\ y\ge0\},
--   $$
--
--   with their $m+n$ inequalities in the order of the labels. The label of a point is the set of its binding inequalities (p.7). The standing assumption is that $P$ and $Q$ are bounded.
--   3. **Equilibria** (Definition 1, p.7). $(x,y)\in P\times Q$ is an equilibrium if every label appears at $x$ or $y$. This includes the artificial equilibrium $(0,0)$. $x$ is an **equilibrium vertex** of $P$ if $(x,y)$ is an equilibrium for some $y$.
--   4. **Labeled facets and projective equivalence** (Lemma 4, p.8). The hypothesis that each row defines its own facet, the completely labeled vertex pairs of two labeled systems, and bijective projective maps $z\mapsto(Mz+c)/(\langle w,z\rangle+\delta)$ with positive denominator that preserve labels and face lattices.
--
--   These objects translate counting Nash equilibria into a combinatorial question on $P$ and $Q$.
--
--   **Formalization Note** The labels $[m+n]$ are `Fin m ⊕ Fin n`, with $i\le m$ as `Sum.inl` and $m+j$ as `Sum.inr`, both zero-based. The inequality $x\ge0$ is written $-x\le0$, as in (5). A pure strategy is a best response when it maximizes the corresponding entry of $x^\top B$ or $Ay$, and supports are the nonzero entries.
-- source:
--   Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3, p.5; display (3), p.6; p.7, Definition 1; p.8, Lemma 4; p.11

import Mathlib
import Definitions.Def_RankOneBimatrix_BinSearch_Game
import Definitions.Def_BimatrixStableSet_Polyhedra

open Matrix RankOneBimatrix.BinSearch

namespace BimatrixStableSet

variable {m n : ℕ}

/-- A bimatrix game is non-degenerate if for any mixed strategy `z` of a player there are at most
`|supp(z)|` many pure strategies that are best responses to `z`, p.5 (Ickstadt, Theobald, von
Stengel, arXiv:2411.12385v3).

**Formalization Note.** A pure strategy `j` of player 2 is a best response to `x` when it maximizes
`(x⊤B)ⱼ`, and a pure strategy `i` of player 1 is a best response to `y` when it maximizes `(Ay)ᵢ`.
Both players are covered, over all mixed strategies. -/
def IsNondegenerate (A B : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  (∀ x ∈ Mixed m, {j | ∀ k, (x ᵥ* B) k ≤ (x ᵥ* B) j}.ncard ≤ {i | x i ≠ 0}.ncard) ∧
  (∀ y ∈ Mixed n, {i | ∀ k, (A *ᵥ y) k ≤ (A *ᵥ y) i}.ncard ≤ {j | y j ≠ 0}.ncard)

/-- The polyhedron `P = {x ∈ ℝᵐ | x ≥ 0, B⊤x ≤ 1}` of display (3), p.6, with its `m + n` inequalities
in the order of the labels.

**Formalization Note.** The labels `[m + n]` are encoded as `Fin m ⊕ Fin n`: the label `i ∈ [m]` is
`Sum.inl` of index `i - 1`, and the label `m + j` is `Sum.inr` of index `j - 1`. The inequality
`x ≥ 0` is written `-x ≤ 0`, as in display (5). -/
def bestResponseP (B : Matrix (Fin m) (Fin n) ℝ) : System (Fin m ⊕ Fin n) m :=
  ⟨Matrix.fromRows (-1) Bᵀ, Sum.elim 0 1⟩

/-- The polyhedron `Q = {y ∈ ℝⁿ | Ay ≤ 1, y ≥ 0}` of display (3), p.6, with its labels. -/
def bestResponseQ (A : Matrix (Fin m) (Fin n) ℝ) : System (Fin m ⊕ Fin n) n :=
  ⟨Matrix.fromRows A (-1), Sum.elim 1 0⟩

/-- The polyhedra `P` and `Q` of (3) are polytopes, the assumption of §3, p.6. -/
def HasBestResponsePolytopes (A B : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  Bornology.IsBounded (bestResponseP B).carrier ∧ Bornology.IsBounded (bestResponseQ A).carrier

/-- Definition 1, p.7: `(x, y) ∈ P × Q` is completely labeled, or an equilibrium of the game, if
every element of `[m + n]` appears as a label of `x` or `y`. This includes the artificial equilibrium
`(0, 0)`. -/
def IsEquilibrium (A B : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) : Prop :=
  x ∈ (bestResponseP B).carrier ∧ y ∈ (bestResponseQ A).carrier ∧
    ∀ k, k ∈ (bestResponseP B).labels x ∨ k ∈ (bestResponseQ A).labels y

/-- The set of equilibria of Definition 1, including `(0, 0)`. -/
def equilibria (A B : Matrix (Fin m) (Fin n) ℝ) : Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | IsEquilibrium A B p.1 p.2}

/-- `x` is an equilibrium vertex of `P`: `(x, y)` is an equilibrium for some `y`, p.11. -/
def IsEquilibriumVertex (A B : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) : Prop :=
  ∃ y, IsEquilibrium A B x y

/-- Each label in `L` is the label of exactly one facet: every row defines a facet of the whole
polyhedron, and different rows define different facets. This is the hypothesis "each with `m + n`
facets labeled `1, …, m + n`" of Lemma 4, p.8, together with the count in `IsSimplePolytope`. -/
def IsFacetLabeled {L : Type} {N : ℕ} (Z : System L N) : Prop :=
  (∀ l, Z.IsFacetOf (Z.face {l}) Z.carrier) ∧ Function.Injective fun l => Z.face {l}

/-- The completely labeled vertex pairs of `P × Q`, for two labeled systems, p.8. -/
def completelyLabeledPairs {L : Type} {M N : ℕ} (P : System L M) (Q : System L N) :
    Set ((Fin M → ℝ) × (Fin N → ℝ)) :=
  {p | p.1 ∈ P.vertices P.carrier ∧ p.2 ∈ Q.vertices Q.carrier ∧
    ∀ l, l ∈ P.labels p.1 ∨ l ∈ Q.labels p.2}

/-- The projective map `z ↦ (Mz + c) / (⟨w, z⟩ + δ)`. Display (4), p.8, is the case `M = 1`, `c = 0`,
`w = α1`, `δ = 1`. -/
noncomputable def projectiveMap {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (c w : Fin N → ℝ) (δ : ℝ)
    (z : Fin N → ℝ) : Fin N → ℝ :=
  (w ⬝ᵥ z + δ)⁻¹ • (M *ᵥ z + c)

/-- A bijective projective transformation between two labeled polytopes that leaves the face lattice
unchanged, Lemma 4(b), p.8: a projective map with positive denominator on the polytope, a bijection
of the polytopes, preserving the labels of every point. -/
def IsProjectiveEquivalence {L : Type} {N : ℕ} (Z Z' : System L N) : Prop :=
  (∃ (M : Matrix (Fin N) (Fin N) ℝ) (c w : Fin N → ℝ) (δ : ℝ),
    (∀ z ∈ Z.carrier, 0 < w ⬝ᵥ z + δ) ∧
    Set.BijOn (projectiveMap M c w δ) Z.carrier Z'.carrier ∧
    ∀ z ∈ Z.carrier, ∀ l, l ∈ Z.labels z ↔ l ∈ Z'.labels (projectiveMap M c w δ z)) ∧
  Z.SameType Z.carrier Z' Z'.carrier

end BimatrixStableSet


