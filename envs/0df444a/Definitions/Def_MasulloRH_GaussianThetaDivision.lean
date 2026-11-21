-- Prove2me | Definitions.Def_MasulloRH_GaussianThetaDivision
-- name    : MasulloRH_GaussianThetaDivision
-- status  : Definition
-- author  : @marozols
-- created : 2026-11-21T03:58:59.332746+00:00
-- url     : https://prove2.me/theorems/2ac9f610-07e0-499f-a791-cff8f32571cb
-- title:
--   The explicit dyadic theta seed, quartic smoothing kernel and zeta moment conditions
-- statement:
--   The seed is the centered logarithmic theta series for the dyadic Gaussian with coefficients 1, −3, 2 at scales 1, 2, 4. The smoothing kernel is the physical dilation of the inverse Fourier transform of exp(−(2πξ)^4). A function satisfies the divisor moment conditions if its bilateral Laplace moments vanish through each interior zeta multiplicity. Quantitative wall separation measures Euclidean distance from both vertical lines to nearby nontrivial zeros.
-- source:
--   Explicit physical kernels used in the rational specialization of Masullo’s Sections 9 and 10. The dyadic seed has verified Mellin factorization in Prove2Me theorem MasulloRH.dyadic_gaussian_theta_mellin, 714a2f7b.

import Mathlib

open MeasureTheory FourierTransform
open scoped FourierTransform

namespace MasulloRH
noncomputable section

/-- The centered rational theta sum of the two-moment dyadic Gaussian test. -/
def rationalDyadicThetaSeed (x : ℝ) : ℂ :=
  (Real.exp (x/2):ℂ) * ∑' n : ℤ, let t := (n:ℝ)*Real.exp x
    ((Real.exp (-Real.pi*t^2) - 3*Real.exp (-Real.pi*(2*t)^2) +
      2*Real.exp (-Real.pi*(4*t)^2) : ℝ) : ℂ)

/-- The dilation by ε of the inverse Fourier transform of exp(−(2πξ)⁴),
in Mathlib's ordinary-frequency convention. -/
def rationalQuarticKernel (ε x : ℝ) : ℂ :=
  ((ε⁻¹:ℝ):ℂ) * (𝓕⁻ (fun ξ : ℝ => (Real.exp (-((-2*Real.pi*ξ)^4)):ℂ))) (ε⁻¹*x)

/-- Vanishing of the bilateral Laplace moments of f through the multiplicities
of every nontrivial zeta zero strictly between the two specified walls. -/
def RationalStripDivisorMoments (b : ℝ) (f : ℝ→ℂ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ=0 → 0<ρ.re → ρ.re<1 → |ρ.re-1/2|<b →
    ∀ r : ℕ, r<analyticOrderNatAt riemannZeta ρ →
      (∫ x : ℝ, f x*(x:ℂ)^r*Complex.exp ((ρ-1/2)*(x:ℂ)))=0

/-- The walls Re(s)=1/2±b stay at distance at least d/(1+|t|)² from each
nontrivial zeta zero with ordinate within three units of t. -/
def RationalZetaWallsSeparated (d b : ℝ) : Prop :=
  ∀ t : ℝ, ∀ u : ℝ, u=b ∨ u= -b → ∀ ρ : ℂ,
    riemannZeta ρ=0 → 0<ρ.re → ρ.re<1 → |ρ.im-t|≤3 →
      d/(1+|t|)^2 ≤ ‖(u:ℂ)+(t:ℂ)*Complex.I+1/2-ρ‖

end
end MasulloRH


