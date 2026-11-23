-- Prove2me | Definitions.Def_MaxLatticeFree_Geometry_Supplement_Extreme
-- name    : MaxLatticeFree_Geometry_Supplement_Extreme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:59:35.296573+00:00
-- url     : https://prove2.me/theorems/e4841ecd-1536-47c3-b8ce-ac1f1f3f9df7
-- title:
--   Extreme valid inequalities, for $R_f(W)$ and for a set in finite dimension
-- statement:
--   Let $f\in\mathbb R^q$ and $W\subseteq\mathbb R^q$ a linear subspace. A valid inequality $\sum_{r\in W}\psi(r)s_r\ge1$ for $R_f(W)$ is **extreme** if there do not exist distinct functions $\psi_1,\psi_2:W\to\mathbb R$ with
--
--   $$
--   \psi\ \ge\ \tfrac12(\psi_1+\psi_2)\quad\text{pointwise on }W
--   $$
--
--   such that $\sum_{r}\psi_i(r)s_r\ge1$ is valid for $R_f(W)$ for $i=1,2$.
--
--   For a set $X\subseteq\mathbb R^m$ (in the paper $X=\operatorname{conv}(R_f(r^1,\dots,r^m))$), an inequality $\sum_j c_js_j\ge1$ is **extreme for $X$** if it holds on $X$ and there are no distinct $\alpha,\beta\in\mathbb R^m$ with $\tfrac12(\alpha_j+\beta_j)\le c_j$ for every $j$ such that $\sum_j\alpha_js_j\ge1$ and $\sum_j\beta_js_j\ge1$ both hold on $X$.
--
--   Extreme inequalities are the ones needed to describe the closed convex hull; Theorem 5 compares the two notions.
--
--   **Formalization Note** Validity of the inequality itself is part of both definitions. The comparison with $\psi$ (resp. $c$) is the pointwise inequality $\le$, as on p. 7, not an equality.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 7, definition of an extreme inequality (after Gomory and Johnson); finite form as used on p. 24

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_ValidInequalities

namespace MaxLatticeFree.Geometry.Supplement

open MaxLatticeFree.Inequalities

/-- Extreme valid inequality for `R_f(W)` (arXiv:1701.06543v1, p. 7, after Gomory–Johnson): the
inequality `∑_{r ∈ W} ψ(r) s_r ≥ 1` is valid for `R_f(W)`, and there are no distinct
`ψ₁, ψ₂ : W → ℝ` with `ψ ≥ ½(ψ₁ + ψ₂)` such that `∑ ψᵢ(r) s_r ≥ 1` is valid for both `i`. -/
noncomputable def IsExtreme {q : ℕ} (f : EuclideanSpace ℝ (Fin q))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (ψ : W → ℝ) : Prop :=
  IsValid f W ψ 1 ∧
    ∀ ψ₁ ψ₂ : W → ℝ, IsValid f W ψ₁ 1 → IsValid f W ψ₂ 1 →
      (∀ r, (ψ₁ r + ψ₂ r) / 2 ≤ ψ r) → ψ₁ = ψ₂

/-- Extreme inequality for a set `X ⊆ ℝᵐ` (the definition of p. 7 applied to a finite problem, as
used on p. 24 of arXiv:1701.06543v1): `∑_j c_j s_j ≥ 1` is satisfied by every `s ∈ X`, and there
are no distinct `α, β ∈ ℝᵐ` with `½(α_j + β_j) ≤ c_j` for every `j` such that `∑_j α_j s_j ≥ 1` and
`∑_j β_j s_j ≥ 1` both hold on `X`. -/
def IsExtremeFinite {m : ℕ} (X : Set (Fin m → ℝ)) (c : Fin m → ℝ) : Prop :=
  (∀ s ∈ X, 1 ≤ ∑ j, c j * s j) ∧
    ∀ α β : Fin m → ℝ, (∀ s ∈ X, 1 ≤ ∑ j, α j * s j) → (∀ s ∈ X, 1 ≤ ∑ j, β j * s j) →
      (∀ j, (α j + β j) / 2 ≤ c j) → α = β

end MaxLatticeFree.Geometry.Supplement


