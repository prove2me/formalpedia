-- Prove2me | Definitions.Def_CritWinSpin_SamplerAnalyticData
-- name    : CritWinSpin_SamplerAnalyticData
-- status  : Definition
-- author  : @Maxliu
-- created : 2026-11-17T18:06:33.396201+00:00
-- url     : https://prove2.me/theorems/9e46734b-39e4-4f9d-9ef2-5d2857671e73
-- title:
--   Analytic data for the finite Langevin sampler in Theorem 4.4
-- statement:
--   Let $U$ be a potential on $\mathbb R^N$. The associated Gibbs measure is
--
--   $$\mu_U(dx)=\frac{e^{-U(x)}}{\int e^{-U(z)}\,dz}\,dx.$$
--
--   These definitions give the Gibbs measure, the regularized Ising potential and its gradient, and the analytic certificate used in the proof of Theorem 4.4. The certificate records continuity, density integrability, strong monotonicity, a quadratic Taylor bound, a Lipschitz bound, and the required first and sixth moments. The Gaussian sixth-moment constant is shared by the discretization estimates.
--
--   The potential is the regularization of $W$ from equation (23); the certificate supports the finite Langevin construction used to obtain the sampler in equation (24).
-- source:
--   Liu–Zhang–Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Section 4, pp.14–17, equations (23)–(24). Analytic data for the proof of Theorem 4.4.

import Mathlib
import Definitions.Def_CritWinSpin_Wpot

set_option autoImplicit false
set_option linter.all false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace CritWinSpin.Implementation.DensityAnalysis

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

def gibbsDensity {d : ℕ} (V : Point d → ℝ) (x : Point d) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-V x))

def partition {d : ℕ} (V : Point d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, gibbsDensity V x ∂volume

def gibbs {d : ℕ} (V : Point d → ℝ) : Measure (Point d) :=
  (partition V)⁻¹ • volume.withDensity (gibbsDensity V)

end CritWinSpin.Implementation.DensityAnalysis

namespace CritWinSpin.Implementation.EnvelopeGeometry

def grad {N : ℕ} (S : SpinLaw) (s a : ℝ) (L : Matrix (Fin N) (Fin N) ℝ)
    (h z : Fin N → ℝ) : Fin N → ℝ :=
  (1 + a) • z - L.transpose.mulVec (fun i => deriv (phis S s) (L.mulVec z i + h i))

abbrev Point (N : ℕ) := EuclideanSpace ℝ (Fin N)

def potential {N : ℕ} (S : SpinLaw) (s a : ℝ) (L : Matrix (Fin N) (Fin N) ℝ)
    (h : Fin N → ℝ) (z : Point N) : ℝ :=
  Ualpha S s a L h (fun i => z i)

def gradient {N : ℕ} (S : SpinLaw) (s a : ℝ) (L : Matrix (Fin N) (Fin N) ℝ)
    (h : Fin N → ℝ) (z : Point N) : Point N :=
  WithLp.toLp 2 (grad S s a L h (fun i => z i))

end CritWinSpin.Implementation.EnvelopeGeometry

namespace CritWinSpin.Implementation.LangevinBudget
open DensityAnalysis

structure Certificate (d : ℕ) (a : ℝ) where
  U : Point d → ℝ
  g : Point d → Point d
  continuous_U : Continuous U
  continuous_g : Continuous g
  density_integrable : Integrable (fun x => Real.exp (-U x))
  monotone : ∀ x y, a * ‖x - y‖ ^ 2 ≤ inner ℝ (x - y) (g x - g y)
  taylor : ∀ x y, |U y - U x - inner ℝ (y - x) (g x)| ≤ ‖y - x‖ ^ 2
  lipschitz : ∀ x y, ‖g x - g y‖ ≤ 4 * ‖x - y‖
  grad_integrable : Integrable (fun x => ‖g x‖ ^ 6) (DensityAnalysis.gibbs U)
  norm_integrable : Integrable (fun x => ‖x‖) (DensityAnalysis.gibbs U)

end CritWinSpin.Implementation.LangevinBudget

namespace CritWinSpin.Implementation.GaussianMoments

def sixthConstant : ℝ := ∫ x : ℝ, |x| ^ 6 ∂gaussianReal 0 1

end CritWinSpin.Implementation.GaussianMoments

end


