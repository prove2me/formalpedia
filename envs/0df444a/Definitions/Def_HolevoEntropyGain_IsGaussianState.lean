-- Prove2me | Definitions.Def_HolevoEntropyGain_IsGaussianState
-- name    : HolevoEntropyGain_IsGaussianState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:50.868463+00:00
-- url     : https://prove2.me/theorems/84b66ae1-c0ab-438d-933c-0206f450829b
-- title:
--   Gaussian state with zero mean and covariance matrix $\alpha$
-- statement:
--   Let $W$ be a Weyl system for $\Delta$ on $\ell^2(I)$ and let $\alpha$ be a real $2s\times 2s$ matrix. An operator $\rho$ on $\ell^2(I)$ is the density operator of the **Gaussian state with zero mean and covariance matrix $\alpha$** if
--
--   1. $\rho$ is a density operator (positive, trace class, trace one);
--   2. $\alpha$ is real (symmetric) positive definite;
--   3. $\alpha \pm \tfrac i2\Delta \ge 0$ as complex Hermitian matrices (the uncertainty relation);
--   4. the characteristic function of $\rho$ is
--   $$
--   \operatorname{Tr}\rho\, W(z) = \exp\!\Big(-\tfrac12\, z^\top\alpha z\Big), \qquad z\in\mathbb R^{2s}. \tag{13}
--   $$
--
--   **Formalization Note** $\rho$ is a coefficient array, so that the Gibbs array $\rho_\beta$ and channel outputs $\Phi[\rho]$ can be called Gaussian directly. Condition 2 is the paper's; with $\det\Delta\neq0$ it also follows from condition 3.
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, eq. (13), p.4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_HolevoEntropyGain_weylCharacteristic

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open Matrix
open scoped ComplexOrder

namespace HolevoEntropyGain

/-- `X` is the density operator of the Gaussian state with zero mean and covariance matrix `α`: `α` is
real positive definite with `α ± (i/2)Δ ≥ 0`, and `Tr X W(z) = exp(-½ zᵀαz)`
(Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, eq. (13), p.4, PDF p.4).

**Formalization Note** `X` is an array so that the Gibbs array `ρ_β` and an output `Φ[ρ]` can be called
Gaussian directly; `density` makes it a density operator. -/
structure IsGaussianState {I : Type} {s : ℕ} {Δ : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ}
    (W : WeylSystem I Δ) (α : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ) (X : Matrix I I ℂ) : Prop where
  /-- `X` is a density operator. -/
  density : IsDensity X
  /-- `α` is real positive definite. -/
  posDef : α.PosDef
  /-- `α + (i/2)Δ ≥ 0`. -/
  uncertainty_plus : (α.map Complex.ofReal + (Complex.I / 2) • Δ.map Complex.ofReal).PosSemidef
  /-- `α - (i/2)Δ ≥ 0`. -/
  uncertainty_minus : (α.map Complex.ofReal - (Complex.I / 2) • Δ.map Complex.ofReal).PosSemidef
  /-- (13). -/
  characteristic : ∀ z, weylCharacteristic W X z =
    Complex.exp (-(1 / 2) * ((z ⬝ᵥ α *ᵥ z : ℝ) : ℂ))

end HolevoEntropyGain


