-- Prove2me | Definitions.Def_ScalarMultiRisk_pointwiseDual
-- name    : ScalarMultiRisk_pointwiseDual
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:03.041241+00:00
-- url     : https://prove2.me/theorems/aa160fae-2f18-45cd-90bd-69c76b42d6b3
-- title:
--   The pointwise dual cone $K_t^+(\omega)$
-- statement:
--   $K_t^+(\omega)=\{y\in\mathbb R^d\mid y^{\mathsf T}x\ge0\ \text{for all }x\in K_t(\omega)\}$ is the dual cone of $K_t(\omega)$.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, (4.3), p.18

import Mathlib
import Definitions.Def_ScalarMultiRisk_Market

open MeasureTheory Matrix

namespace ScalarMultiRisk

/-- **The pointwise dual cone `K_t⁺(ω)`.** arXiv:1807.10694v5, (4.3), p.18:
`K_t⁺(ω) = {y ∈ ℝ^d | yᵀx ≥ 0 ∀ x ∈ K_t(ω)}`. -/
def pointwiseDual {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} (A : Market Ω T d)
    (t : Fin (T + 1)) (ω : Ω) : Set (Fin d → ℝ) :=
  {y | ∀ x ∈ A.K t ω, 0 ≤ y ⬝ᵥ x}

end ScalarMultiRisk


