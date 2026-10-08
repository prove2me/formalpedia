-- Prove2me | Definitions.Def_SmoothedSimplex_Shadow_planeDensity
-- name    : SmoothedSimplex_Shadow_planeDensity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:05:45.333423+00:00
-- url     : https://prove2.me/theorems/95b9c2c2-4fd2-4f9e-a9e3-cbcd78d1bf3f
-- title:
--   §4 — the factor $\prod_{i=1}^d\mu_i(R_\omega b_i+sq)$
-- statement:
--   Fix a reference unit vector $q\in\mathbb R^d$, a coordinatization $\varphi:\mathbb R^{d-1}\to q^\perp$ (a linear isometry onto the orthogonal complement of $q$), and the Gaussian densities $\mu_1,\dots,\mu_d$ of standard deviation $\sigma$ centered at $\bar a_1,\dots,\bar a_d$. For a unit vector $\omega$, a real $s$ and points $b_1,\dots,b_d\in\mathbb R^{d-1}$, this is
--
--   $$
--   \prod_{i=1}^{d}\mu_i\big(R_\omega b_i+sq\big),
--   $$
--
--   where $b_i$ is viewed as the vector $\varphi(b_i)\in q^\perp\subseteq\mathbb R^d$ and $R_\omega$ is the rotation taking $q$ to $\omega$. It is the joint density of $a_1,\dots,a_d$ expressed in the variables $(\omega,s,b_1,\dots,b_d)$ of Corollary 2.5.3.
--
--   **Formalization Note** The paper calls the coordinatization of $q^\perp$ arbitrary; it is the parameter $\varphi$ here, and the statements that use this factor hold for every $\varphi$. Indices are 0-based.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, densities of Lemmas 4.1.1 (p. 45), 4.2.1 and 4.2.2 (p. 52); change of variables §2.5, pp. 25–26

import Mathlib
import Definitions.Def_SmoothedSimplex_Shadow_gaussianPdf
import Definitions.Def_SmoothedSimplex_Shadow_rotTo

namespace SmoothedSimplex.Shadow

/-- The factor `∏_{i=1}^d µ_i(R_ω bᵢ + sq)` that appears in the densities of Lemmas 4.1.1, 4.2.1
and 4.2.2 (Spielman & Teng, arXiv:cs/0111050v7, printed pp. 44–53, PDF pp. 44–53; the change of
variables of Corollary 2.5.3, p. 26). Here `µ_i` is the Gaussian density of standard deviation
`σ` centered at `āᵢ`, `bᵢ ∈ ℝ^{d−1}` is viewed as an element of the subspace orthogonal to the
reference unit vector `q` through the coordinatization `φ : ℝ^{d−1} ≃ q^⊥`, and `R_ω` is
`rotTo q ω`.

**Formalization Note.** Indices are 0-based: the paper's `i ∈ {1, …, d}` are the `i : Fin n`
with `i < d`, and `b : Fin d → ℝ^{d−1}`. The paper calls the coordinatization of `q^⊥` arbitrary;
here it is the parameter `φ`, a linear isometry onto `q^⊥`, and every statement using this
factor quantifies over it. Values are in `ℝ≥0∞`. -/
noncomputable def planeDensity {d n : ℕ} (q : EuclideanSpace ℝ (Fin d))
    (φ : EuclideanSpace ℝ (Fin (d - 1)) ≃ₗᵢ[ℝ] (Submodule.span ℝ {q})ᗮ)
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (σ : ℝ) (ω : EuclideanSpace ℝ (Fin d)) (s : ℝ)
    (b : Fin d → EuclideanSpace ℝ (Fin (d - 1))) : ENNReal :=
  ∏ i : Fin n, if h : i.val < d then
    ENNReal.ofReal (gaussianPdf (abar i) σ (rotTo q ω (φ (b ⟨i.val, h⟩) : EuclideanSpace ℝ (Fin d)) + s • q))
  else 1

end SmoothedSimplex.Shadow


