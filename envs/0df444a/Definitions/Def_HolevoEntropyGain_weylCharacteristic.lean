-- Prove2me | Definitions.Def_HolevoEntropyGain_weylCharacteristic
-- name    : HolevoEntropyGain_weylCharacteristic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:18:09.366349+00:00
-- url     : https://prove2.me/theorems/c01f32c2-a343-4c8c-9cd5-3fd73c5080a0
-- title:
--   Characteristic function $\varphi_X(z) = \operatorname{Tr} X W(z)$
-- statement:
--   Let $W$ be a Weyl system on $\ell^2(I)$ for the commutation matrix $\Delta$. The **characteristic function** of a trace-class operator $X$ is
--
--   $$
--   \varphi_X(z) = \operatorname{Tr} X\,W(z), \qquad z\in\mathbb R^{2s}.
--   $$
--
--   For a density operator $\rho$ it is the quantum analogue of the characteristic function of a probability distribution; Gaussian states and Gaussian channels are defined through it.
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, eq. (13), p.4

import Mathlib
import Definitions.Def_HolevoEntropyGain_WeylSystem
import Definitions.Def_HolevoEntropyGain_tracePairing

open QAlgorithms.RealRegisters (Hilbert)

namespace HolevoEntropyGain

/-- The characteristic function `φ_X(z) = Tr X W(z)` of a trace-class operator `X`
(Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, eq. (13), p.4, PDF p.4). -/
noncomputable def weylCharacteristic {I : Type} {s : ℕ}
    {Δ : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ} (W : WeylSystem I Δ) (X : Matrix I I ℂ)
    (z : Fin (2 * s) → ℝ) : ℂ :=
  tracePairing X (W.operator z)

end HolevoEntropyGain


