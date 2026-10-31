-- Prove2me | Definitions.Def_KnapsackFacets_KnapsackPolytope
-- name    : KnapsackFacets_KnapsackPolytope
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:45.335477+00:00
-- url     : https://prove2.me/theorems/cbbdb432-c1db-4f48-86d4-560f9047bb99
-- title:
--   Knapsack set, knapsack polytope, valid and facet-defining inequalities
-- statement:
--   For $a\in\mathbb N^n$ and $b\in\mathbb N$, the **knapsack set** is $Q=\{x\in\{0,1\}^n : a^\top x\le b\}$ and the **knapsack polytope** (KP) is its convex hull $P=\operatorname{conv}(Q)\subseteq\mathbb R^n$.
--
--   For $\alpha\in\mathbb Z^n$ and $\beta\in\mathbb Z$, the inequality $\alpha^\top x\le\beta$ is **valid** for $P$ when it holds at every point of $P$; its **face** is $F=P\cap\{x:\alpha^\top x=\beta\}$. The inequality is **facet-defining** for $P$ when it is valid, $F$ is nonempty, and
--   $$
--   \dim F=\dim P-1 ,
--   $$
--   dimensions being those of affine hulls.
--
--   These are the polyhedral notions of the decision problem KNAPSACK FACETS and of every Claim in the proof of Theorem 4.
--
--   **Formalization Note** Points are `Fin n → ℝ` (coordinate $i$ is the paper's $x_{i+1}$). The coefficients $a_i$ may be zero here, because the proof of Theorem 4 works with vectors $a_i=(t+1)w_i$, $w_i\ge0$; the positivity of $a$ and $b$ is imposed by the language KNAPSACK FACETS. $\dim F=\dim P-1$ is written $\dim F+1=\dim P$, and nonemptiness of $F$ is required explicitly.
-- source:
--   Chen & Zhu, The Complexity of Recognizing Facets for the Knapsack Polytope, arXiv:2211.03311v3, p.2 (facet-defining inequality), p.3 (knapsack set, KP), p.6 (KP conv({x ∈ {0, 1}ᴺ : a⊤x ≤ b}))

import Mathlib

set_option autoImplicit false

namespace KnapsackFacets

/-- **Knapsack set** `{x ∈ {0,1}ⁿ : aᵀx ≤ b}`. Chen & Zhu, arXiv:2211.03311v3, §2, p.3:
"we call the set {x ∈ {0, 1}ⁿ : a⊤x ≤ b} with (a, b) ∈ ℕⁿ⁺¹ a knapsack set."

**Formalization Note.** Points are `Fin n → ℝ` (coordinate `i` is the paper's `x_{i+1}`).
The coefficients are natural numbers *including zero*: the polyhedral statements of the
proof of Theorem 4 (Claims B–D, (i), (ii)) are about vectors with possibly zero entries
`aᵢ = (t+1)wᵢ`; the positivity `aᵢ ≥ 1`, `b ≥ 1` of the paper's knapsack sets is imposed by
the language `KNAPSACK_FACETS`. -/
def knapsackSet {n : ℕ} (a : Fin n → ℕ) (b : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, x i = 0 ∨ x i = 1) ∧ ∑ i, (a i : ℝ) * x i ≤ b}

/-- **Knapsack polytope** `KP = conv({x ∈ {0,1}ⁿ : aᵀx ≤ b})`. Chen & Zhu,
arXiv:2211.03311v3, p.6 ("a KP conv({x ∈ {0, 1}ᴺ : a⊤x ≤ b})"). -/
def KP {n : ℕ} (a : Fin n → ℕ) (b : ℕ) : Set (Fin n → ℝ) :=
  convexHull ℝ (knapsackSet a b)

/-- **Validity**: `αᵀx ≤ β` holds at every point of the knapsack polytope. Chen & Zhu,
arXiv:2211.03311v3, p.2 and p.3 ("this inequality is valid for the associated KP"). -/
def IsValid {n : ℕ} (a : Fin n → ℕ) (b : ℕ) (α : Fin n → ℤ) (β : ℤ) : Prop :=
  ∀ x ∈ KP a b, ∑ i, (α i : ℝ) * x i ≤ β

/-- **The face** `KP ∩ {x : αᵀx = β}` cut out by `αᵀx ≤ β`. Chen & Zhu, arXiv:2211.03311v3,
p.3 ("the corresponding hyperplane has a nonempty intersection with the KP"). -/
def face {n : ℕ} (a : Fin n → ℕ) (b : ℕ) (α : Fin n → ℤ) (β : ℤ) : Set (Fin n → ℝ) :=
  KP a b ∩ {x | ∑ i, (α i : ℝ) * x i = β}

/-- **Facet-defining inequality.** `αᵀx ≤ β` is facet-defining for `P = KP a b` when it is
valid for `P`, the face `F = P ∩ {αᵀx = β}` is nonempty, and `dim F = dim P − 1`.
Chen & Zhu, arXiv:2211.03311v3, p.2: "a facet-defining inequality of a polytope P is
essentially a valid inequality that holds at equality at dim(P) affinely independent points
in P."

**Formalization Note.** Dimensions are `Module.finrank` of the `vectorSpan` (the dimension of
the affine hull), and `dim F = dim P − 1` is written `dim F + 1 = dim P`, with no natural-number
subtraction. Nonemptiness of `F` is required explicitly: without it the empty face would be a
facet of a segment, and `0ᵀx ≤ 0` would be facet-defining for every polytope under the literal
reading of p.2. This is the standard notion of a facet. -/
def IsFacetDefining {n : ℕ} (a : Fin n → ℕ) (b : ℕ) (α : Fin n → ℤ) (β : ℤ) : Prop :=
  IsValid a b α β ∧ (face a b α β).Nonempty ∧
    Module.finrank ℝ (vectorSpan ℝ (face a b α β)) + 1 =
      Module.finrank ℝ (vectorSpan ℝ (KP a b))

end KnapsackFacets


