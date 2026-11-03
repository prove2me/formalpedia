-- Prove2me | Definitions.Def_HolevoEntropyGain_IsNondegenerateCovariance
-- name    : HolevoEntropyGain_IsNondegenerateCovariance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:37.387994+00:00
-- url     : https://prove2.me/theorems/7c60dbb2-b2ae-4c82-99ca-639ecd2f6a75
-- title:
--   Nondegenerate Gaussian state: $\alpha - \tfrac i2\Delta > 0$
-- statement:
--   The Gaussian state with covariance matrix $\alpha$ is **nondegenerate** if
--
--   $$
--   \alpha - \tfrac i2 \Delta > 0, \tag{14}
--   $$
--
--   that is, the complex positive semidefinite matrix $\alpha - \frac i2\Delta$ is positive definite. Equivalently its normal-mode decomposition has no pure component.
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, eq. (14), p.4

import Mathlib

open scoped ComplexOrder

namespace HolevoEntropyGain

/-- Condition (14): the Gaussian state with covariance `α` is nondegenerate, that is the complex
positive semidefinite matrix `α - (i/2)Δ` is positive definite
(Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, eq. (14), p.4, PDF p.4). -/
def IsNondegenerateCovariance {s : ℕ} (Δ α : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ) : Prop :=
  (α.map Complex.ofReal - (Complex.I / 2) • Δ.map Complex.ofReal).PosDef

end HolevoEntropyGain


