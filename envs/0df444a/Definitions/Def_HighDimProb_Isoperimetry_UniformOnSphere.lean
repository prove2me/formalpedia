-- Prove2me | Definitions.Def_HighDimProb_Isoperimetry_UniformOnSphere
-- name    : HighDimProb_Isoperimetry_UniformOnSphere
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:38:51.419091+00:00
-- url     : https://prove2.me/theorems/7995e1f5-1534-4078-80a4-b11f39c1db28
-- title:
--   Uniform distribution on a Euclidean sphere
-- statement:
--   This definition operationally characterizes what it means for a random vector to be
--   **uniformly distributed on a Euclidean sphere** of radius $r$ in $\mathbb R^n$, written
--   $X \sim \mathrm{Unif}(r\,S^{n-1})$, which Theorem 5.1.4 takes as its hypothesis (with
--   $r = \sqrt n$).
--
--   Let $(\Omega, \mathcal F, \mathrm{Prob})$ be a probability space and $X : \Omega \to
--   \mathbb R^n$ a random vector. $X$ is **uniform on the sphere of radius $r$** when:
--
--   1. $X$ lies on the sphere $\{x \in \mathbb R^n : \|x\|_2 = r\}$ almost surely, and
--   2. the law of $X$ is invariant under every orthogonal transformation $U$ of $\mathbb R^n$:
--      $U(X)$ has the same distribution as $X$.
--
--   A probability measure on the sphere invariant under the full orthogonal group is unique —
--   it is the normalized surface (Hausdorff) measure — so these two properties pin down the
--   uniform distribution exactly, without constructing that measure explicitly.
--
--   **Formalization Note** This mirrors, for a random point, exactly the operational convention
--   Vershynin uses for a random *subspace* in §5.2.6/§5.3 ("$E$ is uniformly distributed in
--   $G_{n,m}$" is *defined* by rotation invariance of its law): "uniform" is characterized by
--   invariance under the orthogonal group rather than by naming the surface measure directly,
--   since Mathlib has no ready-made Haar/uniform measure construction on a Euclidean sphere of
--   general radius or on the Grassmannian to build from. `≃ₗᵢ[ℝ]` is Mathlib's type of real
--   linear isometric equivalences of $\mathbb R^n$ with itself, i.e. the orthogonal group $O(n)$.
-- source:
--   Vershynin, High-Dimensional Probability (2018), §5.1.1, p. 105 (PDF p. 113), operational convention stated for the analogous Grassmannian case in §5.2.6/§5.3, p. 118 (PDF p. 126)

import Mathlib

open MeasureTheory

namespace HighDimProb.Isoperimetry

/-- `X` is uniformly distributed on the Euclidean sphere of radius `r` in `ℝⁿ`, i.e.
`X ∼ Unif(r · Sⁿ⁻¹)`. Vershynin, *High-Dimensional Probability* (2018), §5.1.1, operationally
characterizes this by two properties: `X` lies on the sphere almost surely, and the law of `X`
is invariant under every orthogonal transformation of `ℝⁿ` — the same rotation-invariance
convention the book uses to define a uniformly-distributed random subspace in §5.2.6/§5.3
(quoted there as `P {E ∈ 𝓔} = P {U(E) ∈ 𝓔}` for orthogonal `U`), applied here to a random
point instead of a random subspace. A rotation-invariant probability measure supported on the
sphere is the normalized surface measure, so this operational property pins down the uniform
distribution uniquely. -/
def IsUniformOnSphere {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) {n : ℕ} (r : ℝ)
    (X : Ω → EuclideanSpace ℝ (Fin n)) : Prop :=
  (∀ᵐ ω ∂Prob, X ω ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) r) ∧
  (∀ U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
    Measure.map (fun ω => U (X ω)) Prob = Measure.map X Prob)

end HighDimProb.Isoperimetry


