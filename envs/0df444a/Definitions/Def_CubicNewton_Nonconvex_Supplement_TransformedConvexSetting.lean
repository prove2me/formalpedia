-- Prove2me | Definitions.Def_CubicNewton_Nonconvex_Supplement_TransformedConvexSetting
-- name    : CubicNewton_Nonconvex_Supplement_TransformedConvexSetting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:59:44.531994+00:00
-- url     : https://prove2.me/theorems/31e6a0b3-d52c-41ce-9b44-396c6f21d07b
-- title:
--   Section 4.3 — nonlinear transformation of a convex function, $\sigma$ and $D$
-- statement:
--   Fix $x_0\in\mathbb R^n$. Let $u:\mathbb R^n\to\mathbb R^n$ be invertible with inverse $v$, so $v(u(x))=x$ and $u(v(z))=z$, and let
--   $$f(x)=\phi(u(x)),$$
--   where $\phi$ is convex on $\mathbb R^n$ with bounded level sets and $u^*$ minimizes $\phi$; then $x^*=v(u^*)$ minimizes $f$. On the transformed level set $S=\{z:\phi(z)\le f(x_0)\}$ the inverse $v$ is differentiable with derivative $v'(z)$, and
--   $$\|v'(z)\|\le\sigma,\qquad \|z-u^*\|\le D\qquad (z\in S).$$
--   The paper sets $\sigma=\max_{z\in S}\|v'(z)\|$ and $D=\max_{z\in S}\|z-u^*\|$; $D$ is a radius in the transformed coordinates, not a diameter of $F$. This is the setting of Lemma 8 and Theorems 8 and 9.
--
--   **Formalization Note** $\sigma$ and $D$ are arbitrary upper bounds of the two maxima, so the paper's values are one admissible choice; no continuity of $v'$ is assumed.
--   Differences from the source:
--   - generalization: Section 4.3 non-degenerate u with differentiable inverse v and exact maxima σ, D → mutually inverse maps, derivatives of v only on S, and arbitrary upper bounds σ and D on S; no derivative premise for u; reason: every source instance supplies these fields; the estimates use only the inverse derivative on convex S, so no continuity of v′ or extra condition on u is needed
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 195, Section 4.3 (definitions of u, v, φ, x*, σ, D)

import Mathlib

namespace CubicNewton.Nonconvex.Supplement

/-- The setting of Section 4.3 of Nesterov–Polyak 2006 (p. 195), "nonlinear transformations of
convex functions", relative to a starting point `x₀`:
* `u : ℝⁿ → ℝⁿ` is invertible with inverse `v` (`v (u x) = x` and `u (v z) = z`);
* `f = φ ∘ u`, where `φ` is convex on `ℝⁿ` with bounded level sets;
* `ustar` (the paper's `u*`) is a minimizer of `φ`, so `x* = v(u*)` minimizes `f`;
* on the transformed level set `S = {z : φ(z) ≤ f(x₀)}` the inverse `v` is differentiable with
  derivative `v' z` (the paper's `v′(z)`), and
  `σ` bounds `‖v′(z)‖` and `D` bounds `‖z − u*‖` on `S`.
The paper takes `σ = max_{z ∈ S} ‖v′(z)‖` and `D = max_{z ∈ S} ‖z − u*‖`; here `σ` and `D` are
any upper bounds of these quantities, so the paper's maxima are one admissible choice. -/
structure TransformedConvexSetting {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (u v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (v' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (ustar : EuclideanSpace ℝ (Fin n)) (σ D : ℝ) : Prop where
  left_inv : ∀ x, v (u x) = x
  right_inv : ∀ z, u (v z) = z
  comp : ∀ x, f x = φ (u x)
  convex : ConvexOn ℝ Set.univ φ
  bdd_level : ∀ c : ℝ, Bornology.IsBounded {z | φ z ≤ c}
  isMin : ∀ z, φ ustar ≤ φ z
  hasDeriv_inv : ∀ z, φ z ≤ f x₀ → HasFDerivAt v (v' z) z
  sigma_bound : ∀ z, φ z ≤ f x₀ → ‖v' z‖ ≤ σ
  radius_bound : ∀ z, φ z ≤ f x₀ → ‖z - ustar‖ ≤ D

end CubicNewton.Nonconvex.Supplement


