-- Prove2me | Definitions.Def_AdaptiveStepIPM_Probabilistic_Model
-- name    : AdaptiveStepIPM_Probabilistic_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:16:52.680893+00:00
-- url     : https://prove2.me/theorems/199b9dd6-0179-4536-ac60-025bf64a7ce6
-- title:
--   Gaussian random subspace and projection model
-- statement:
--   Let $G$ be an $m\times n$ matrix whose entries are independent standard normal variables. Its null space $U=\ker G$ is the sampled subspace. For a fixed Euclidean vector $r\in\mathbb R^n$, let $p$ be its orthogonal projection onto $U$, let $q=r-p$, and write $Pq=(p_jq_j)_{j=1}^n$. For a coordinate vector $z$, define
--
--   $$
--   \|z\|^-_\infty=\big\|(\min\{z_j,0\})_{j=1}^n\big\|_\infty.
--   $$
--
--   An orthogonal frame $F=[g,H]$ consists of a unit first column $g$ and an orthonormal completion $H$. The angular law is the distribution of $\lambda/\|\lambda\|_2$ for a standard Gaussian vector $\lambda$; its value at the Gaussian origin is set to zero. These definitions isolate the random-subspace geometry from the linear program used earlier in the paper.
--
--   **Formalization Note** The Gaussian null-space construction is the example given on printed pages 13–14. Euclidean vectors use the $\ell_2$ norm; coordinate sup norms are defined separately. A matrix with zero rows and a zero Gaussian vector have their ordinary total-function values.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), pp. 2, 4, 12–14, §6; https://doi.org/10.1287/moor.18.4.964

import Mathlib

open MeasureTheory ProbabilityTheory Filter

namespace AdaptiveStepIPM.Probabilistic

/-- Independent standard normal entries on an `m × n` matrix. -/
noncomputable def gaussianMatrix (m n : ℕ) : Measure (Fin m → Fin n → ℝ) :=
  Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin n => gaussianReal 0 1))

/-- The null space of a real matrix, viewed in Euclidean space. -/
noncomputable def kernel (m n : ℕ) (G : Matrix (Fin m) (Fin n) ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  LinearMap.ker (Matrix.toEuclideanLin G)

/-- Projection of `r` on the sampled null space. -/
noncomputable def p (m n : ℕ) (G : Matrix (Fin m) (Fin n) ℝ)
    (r : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (kernel m n G).starProjection r

/-- Projection of `r` on the orthogonal complement. -/
noncomputable def q (m n : ℕ) (G : Matrix (Fin m) (Fin n) ℝ)
    (r : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  r - p m n G r

/-- The componentwise product `Pq` where `P = diag(p)`. -/
noncomputable def pq (m n : ℕ) (G : Matrix (Fin m) (Fin n) ℝ)
    (r : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ :=
  fun j => (p m n G r) j * (q m n G r) j

/-- The usual sup norm on coordinates of a Euclidean vector. -/
noncomputable def supNorm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖(EuclideanSpace.equiv (Fin n) ℝ) x‖

/-- The sup norm of the coordinatewise negative part, `‖z‖⁻_∞`. -/
noncomputable def negSupNorm {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  ‖fun j => min (z j) 0‖

/-- An orthogonal matrix displayed by its first unit column and its other columns.
The coordinate map expresses completeness of the displayed orthonormal columns. -/
structure Frame (n : ℕ) where
  g : EuclideanSpace ℝ (Fin n)
  H : EuclideanSpace ℝ (Fin (n - 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)
  coordinates : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n - 1))
  g_unit : ‖g‖ = 1
  g_orthogonal : ∀ v, inner ℝ g (H v) = 0
  coordinates_H : ∀ v, coordinates (H v) = v
  decomposition : ∀ x, x = (inner ℝ x g) • g + H (coordinates x)

/-- The coefficient of `g` in the projected point minus one. -/
noncomputable def zeta {n m : ℕ} (F : Frame n)
    (G : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  inner ℝ (p m n G (2 • F.g)) F.g - 1

/-- The nonnegative radial coefficient in Lemma 6. -/
noncomputable def eta {n m : ℕ} (F : Frame n)
    (G : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (1 - zeta F G ^ 2)

/-- Angular coordinate of the projected point. At the null event where the
coordinate vanishes, this total function takes the value zero. -/
noncomputable def v {n m : ℕ} (F : Frame n)
    (G : Matrix (Fin m) (Fin n) ℝ) : EuclideanSpace ℝ (Fin (n - 1)) :=
  let w := F.coordinates (p m n G (2 • F.g))
  (‖w‖⁻¹) • w

/-- Uniform spherical law, constructed as the direction of a standard Gaussian.
The value at the Gaussian origin is zero; that point has measure zero in positive dimension. -/
noncomputable def sphereGaussian (k : ℕ) : Measure (EuclideanSpace ℝ (Fin k)) :=
  (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun w => (‖w‖⁻¹) • w)

end AdaptiveStepIPM.Probabilistic


