-- Prove2me | Definitions.Def_HolevoEntropyGain_IsGaussianChannel
-- name    : HolevoEntropyGain_IsGaussianChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:28.712201+00:00
-- url     : https://prove2.me/theorems/61a495b7-9c71-42ce-9355-8c9542166826
-- title:
--   Centered Bosonic Gaussian channel with parameters $K, \mu$
-- statement:
--   Let $W$ be a Weyl system for $\Delta$ on $\ell^2(I)$, $K$ and $\mu$ real $2s\times 2s$ matrices, and $\Phi$ a channel (completely positive trace-preserving map on trace-class operators). $\Phi$ is the **centered Bosonic Gaussian channel** with parameters $K,\mu$ if
--
--   1. $\mu$ is real positive semidefinite;
--   2. $\mu \ge \pm\tfrac i2\big(\Delta - K^\top\Delta K\big)$, i.e. both $\mu - \frac i2(\Delta - K^\top\Delta K)$ and $\mu + \frac i2(\Delta - K^\top\Delta K)$ are positive semidefinite complex matrices; (15)
--   3. the dual channel acts on Weyl operators by $\Phi^*(W(z)) = W(Kz)\exp(-\tfrac12 z^\top\mu z)$, stated in the predual: for every trace-class $X$ and every $z$,
--   $$
--   \operatorname{Tr}\Phi[X]\,W(z) = \operatorname{Tr} X\, W(Kz)\;\exp\!\Big(-\tfrac12\, z^\top\mu z\Big).
--   $$
--
--   Condition (15) is exactly what makes the map on Weyl operators completely positive; the class contains attenuators, amplifiers and additive classical Gaussian noise.
--
--   **Formalization Note** The dual law is stated in the predual, for every trace-class input. Weyl operators generate the bounded operators weakly (irreducibility) and $\Phi^*$ is normal, so the two forms are equivalent.
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, eq. (15), p.5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_HolevoEntropyGain_weylCharacteristic

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsTraceClass)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open Matrix
open scoped ComplexOrder

namespace HolevoEntropyGain

/-- `Φ` is the centered Bosonic Gaussian channel with parameters `K, μ`:
`Φ*(W(z)) = W(Kz) exp(-½ zᵀμz)`, where the real positive semidefinite `μ` satisfies
`μ ≥ ±(i/2)(Δ - KᵀΔK)` (Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, eq. (15), p.5, PDF p.5).

**Formalization Note** (R2) The dual law is stated in the predual: `Tr Φ[X] W(z) = Tr X W(Kz) exp(-½ zᵀμz)`
for every trace-class `X` and every `z`. Weyl operators generate the bounded operators weakly and `Φ*`
is normal, so the two are equivalent. (15) is the two inequalities `μ ∓ (i/2)(Δ - KᵀΔK) ≥ 0` of
Hermitian complex matrices. -/
structure IsGaussianChannel {I : Type} {s : ℕ} {Δ : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ}
    (W : WeylSystem I Δ) (K μ : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ) (Φ : Channel I I) : Prop where
  /-- `μ` is real positive semidefinite. -/
  noise_posSemidef : μ.PosSemidef
  /-- `μ ≥ (i/2)(Δ - KᵀΔK)`. -/
  noise_plus : (μ.map Complex.ofReal -
    (Complex.I / 2) • (Δ - K.transpose * Δ * K).map Complex.ofReal).PosSemidef
  /-- `μ ≥ -(i/2)(Δ - KᵀΔK)`. -/
  noise_minus : (μ.map Complex.ofReal +
    (Complex.I / 2) • (Δ - K.transpose * Δ * K).map Complex.ofReal).PosSemidef
  /-- The Gaussian law, in the predual. -/
  law : ∀ X, IsTraceClass X → ∀ z, weylCharacteristic W (Φ.val X) z =
    weylCharacteristic W X (K *ᵥ z) * Complex.exp (-(1 / 2) * ((z ⬝ᵥ μ *ᵥ z : ℝ) : ℂ))

end HolevoEntropyGain


