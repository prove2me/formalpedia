-- Prove2me | Definitions.Def_ShortestGCS_Relax_Setting
-- name    : ShortestGCS_Relax_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:57:21.572382+00:00
-- url     : https://prove2.me/theorems/139ac335-9f62-48f1-a70f-6adbaa988180
-- title:
--   Definition 4.8 and (7.1)–(7.3), pp. 6, 12 — valid-inequality cone 𝒳°, dual cone, the bilinear set 𝒮, its relaxation 𝒮′, polyhedra
-- statement:
--   Throughout, $\mathcal X \subseteq \mathbb R^n$ and $\mathcal Y \subseteq \mathbb R^m$, and a point of $\mathbb R^n \times \mathbb R^m \times \mathbb R^{n\times m}$ is written $(x, y, Z)$.
--
--   1. **Cone of valid inequalities** (Definition 4.8): $\mathcal X^\circ := \{(a, b) \in \mathbb R^n \times \mathbb R : a^\top x + b \ge 0 \text{ for all } x \in \mathcal X\}$.
--   2. **Dual cone** of a set $\mathcal K \subseteq \mathbb R^n \times \mathbb R$, for the pairing $\langle (a,b), (x,\lambda)\rangle = a^\top x + b\lambda$: $\mathcal K^* := \{(a, b) : a^\top x + b\lambda \ge 0 \text{ for all } (x, \lambda) \in \mathcal K\}$.
--   3. **Bilinear set** (7.1): $\mathcal S := \{(x, y, Z) : x \in \mathcal X,\ y \in \mathcal Y,\ Z = xy^\top\}$.
--   4. **Set-based relaxation** (7.2):
--   $$
--   \mathcal S' := \{(x, y, Z) : a^\top Z c + d\, a^\top x + b\, c^\top y + bd \ge 0 \text{ for all } (a, b) \in \mathcal X^\circ,\ (c, d) \in \mathcal Y^\circ\}.
--   $$
--   5. **Polyhedron in halfspace form**: for a family $(c_i, d_i)_{i \in \mathcal I}$ with $c_i \in \mathbb R^m$, $d_i \in \mathbb R$, the set $\{y : c_i^\top y + d_i \ge 0 \text{ for all } i \in \mathcal I\}$; a polytope is a bounded one.
--   6. **Asymmetric relaxation** (7.3): $\{(x, y, Z) : (Zc_i + d_i x,\ c_i^\top y + d_i) \in \tilde{\mathcal X} \text{ for all } i \in \mathcal I\}$.
--
--   The relaxation $\mathcal S'$ multiplies every valid inequality of $\mathcal X$ by every valid inequality of $\mathcal Y$ and linearizes the products with $Z = xy^\top$; it is the convex relaxation the paper uses for the bilinear constraints of its mixed-integer formulation.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`, $x^\top y$ is the dot product, $Zc$ is the matrix–vector product and $xy^\top$ is `Matrix.vecMulVec x y`. The inequality in (7.2) is written term for term. The index set of a polyhedron is an arbitrary type; finiteness is assumed by the theorems that need it.
-- source:
--   arXiv:2101.11565v5, Definition 4.8 and the sentence before Lemma 4.9, p. 6; (7.1), (7.2), Proposition 7.1 and (7.3), p. 12

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective

namespace ShortestGCS.Relax

open Matrix

/-- The cone of valid inequalities of a set `𝒳 ⊆ ℝⁿ` (Definition 4.8, arXiv:2101.11565v5, p. 6):
`𝒳° := {(a, b) : aᵀx + b ≥ 0 for all x ∈ 𝒳}`. -/
def validCone {n : ℕ} (X : Set (Fin n → ℝ)) : Set ((Fin n → ℝ) × ℝ) :=
  {ab | ∀ x ∈ X, 0 ≤ ab.1 ⬝ᵥ x + ab.2}

/-- The dual cone `𝒦* := {(a, b) : aᵀx + bλ ≥ 0 for all (x, λ) ∈ 𝒦}` of a set `𝒦 ⊆ ℝⁿ × ℝ`, for the pairing
`((a, b), (x, λ)) ↦ aᵀx + bλ` (arXiv:2101.11565v5, p. 6, the sentence before Lemma 4.9). -/
def dualCone {n : ℕ} (K : Set ((Fin n → ℝ) × ℝ)) : Set ((Fin n → ℝ) × ℝ) :=
  {w | ∀ q ∈ K, 0 ≤ w.1 ⬝ᵥ q.1 + w.2 * q.2}

/-- The bilinear set (7.1), arXiv:2101.11565v5, p. 12:
`𝒮 := {(x, y, Z) : x ∈ 𝒳, y ∈ 𝒴, Z = xyᵀ}`. A triple is `w = (x, y, Z)`. -/
def bilinSet {n m : ℕ} (X : Set (Fin n → ℝ)) (Y : Set (Fin m → ℝ)) :
    Set ((Fin n → ℝ) × (Fin m → ℝ) × Matrix (Fin n) (Fin m) ℝ) :=
  {w | w.1 ∈ X ∧ w.2.1 ∈ Y ∧ w.2.2 = vecMulVec w.1 w.2.1}

/-- The set-based relaxation (7.2), arXiv:2101.11565v5, p. 12:
`𝒮′ := {(x, y, Z) : aᵀZc + d aᵀx + b cᵀy + bd ≥ 0 for all (a, b) ∈ 𝒳° and (c, d) ∈ 𝒴°}`. -/
def relaxSet {n m : ℕ} (X : Set (Fin n → ℝ)) (Y : Set (Fin m → ℝ)) :
    Set ((Fin n → ℝ) × (Fin m → ℝ) × Matrix (Fin n) (Fin m) ℝ) :=
  {w | ∀ ab ∈ validCone X, ∀ cd ∈ validCone Y,
    0 ≤ ab.1 ⬝ᵥ (w.2.2 *ᵥ cd.1) + cd.2 * (ab.1 ⬝ᵥ w.1) + ab.2 * (cd.1 ⬝ᵥ w.2.1) + ab.2 * cd.2}

/-- A polyhedron in halfspace form `{y : cᵢᵀy + dᵢ ≥ 0 for all i ∈ ℐ}` (arXiv:2101.11565v5, p. 12,
Proposition 7.1). A polytope is such a set that is moreover bounded. -/
def polyhedron {m : ℕ} {ι : Type*} (c : ι → Fin m → ℝ) (d : ι → ℝ) : Set (Fin m → ℝ) :=
  {y | ∀ i, 0 ≤ c i ⬝ᵥ y + d i}

/-- The asymmetric relaxation (7.3), arXiv:2101.11565v5, p. 12:
`{(x, y, Z) : (Zcᵢ + dᵢx, cᵢᵀy + dᵢ) ∈ 𝒳̃ for all i ∈ ℐ}`. -/
def asymRelaxSet {n m : ℕ} {ι : Type*} (X : Set (Fin n → ℝ)) (c : ι → Fin m → ℝ) (d : ι → ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ) × Matrix (Fin n) (Fin m) ℝ) :=
  {w | ∀ i, (w.2.2 *ᵥ c i + d i • w.1, c i ⬝ᵥ w.2.1 + d i) ∈ ShortestGCS.MICP.perspectiveSet X}

end ShortestGCS.Relax


