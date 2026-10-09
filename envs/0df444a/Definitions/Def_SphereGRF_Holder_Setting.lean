-- Prove2me | Definitions.Def_SphereGRF_Holder_Setting
-- name    : SphereGRF_Holder_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:35:00.176706+00:00
-- url     : https://prove2.me/theorems/93e9530a-5747-4e05-b535-08f947171606
-- title:
--   Sphere, geodesic distance, Legendre polynomials, covariance kernel and isotropic Gaussian field
-- statement:
--   The unit sphere $S^2$ consists of unit vectors in $\mathbb R^3$. Its distance is $d(x,y)=\arccos\langle x,y\rangle$. The Legendre polynomial $P_\ell$ is given by Rodrigues’ formula. For a nonnegative angular power spectrum $(A_\ell)$, the distance kernel is
--
--   $$
--   k(r)=\sum_{\ell=0}^{\infty} A_\ell\frac{2\ell+1}{4\pi}P_\ell(\cos r),\qquad 0\le r\le\pi.
--   $$
--
--   A random field is jointly measurable on $\Omega\times S^2$. The structure for an isotropic Gaussian field requires Gaussian finite dimensional distributions, constant mean, a nonnegative summable spectrum, and the covariance expansion with this kernel. These objects provide the common setting for the regularity results.
--
--   **Formalization Note** The sphere uses three Cartesian coordinates indexed by $0,1,2$. The covariance expansion represents isotropy for Gaussian fields; the spectrum is specified through covariance rather than Karhunen–Loève coefficients. No centering condition is imposed. The Lean kernel extends to all real $r$; its use for an angular power spectrum is under the summability condition recorded in the field structure.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, Definition 2.1 and setting p. 3; Rodrigues formula p. 4; covariance kernel §3 p. 9; Assumption 4.1 p. 16

import Mathlib
import Definitions.Def_SphereGRF_Spectral_Legendre

open MeasureTheory ProbabilityTheory Polynomial
noncomputable section

namespace SphereGRF.Holder

abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

def geoDist (x y : S2) : ℝ :=
  Real.arccos (inner ℝ (x : EuclideanSpace ℝ (Fin 3)) y)

def kernel (A : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑' ℓ : ℕ, A ℓ * (2 * ℓ + 1) / (4 * Real.pi) * (SphereGRF.Spectral.legendreP ℓ).eval (Real.cos r)

def IsRandomField {Ω : Type*} [MeasurableSpace Ω]
    (_P : Measure Ω) (T : S2 → Ω → ℝ) : Prop :=
  Measurable (fun q : Ω × S2 => T q.2 q.1)

structure IsIsotropicGRF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : S2 → Ω → ℝ) (A : ℕ → ℝ) : Prop where
  randomField : IsRandomField P T
  gaussian : IsGaussianProcess T P
  spec_nonneg : ∀ ℓ, 0 ≤ A ℓ
  spec_summable : Summable (fun ℓ : ℕ => (2 * ℓ + 1) * A ℓ)
  mean_const : ∃ μ : ℝ, ∀ x, ∫ ω, T x ω ∂P = μ
  cov_eq : ∀ x y, cov[T x, T y; P] =
    ∑' ℓ : ℕ, A ℓ * (2 * ℓ + 1) / (4 * Real.pi) *
      (SphereGRF.Spectral.legendreP ℓ).eval (inner ℝ (x : EuclideanSpace ℝ (Fin 3)) y)

end SphereGRF.Holder


