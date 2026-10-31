-- Prove2me | Definitions.Def_ScalarMultiRisk_priceSetStar
-- name    : ScalarMultiRisk_priceSetStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:24:30.012484+00:00
-- url     : https://prove2.me/theorems/9eafd831-c163-4670-860f-3fa9b8195d91
-- title:
--   The set $\mathcal S^*$
-- statement:
--   $\mathcal S^*=\bigcap_{t\ge0}\mathcal S_t$ is the set of eligible price processes for which $\pi^S_t(0)$ is bounded at every time.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Definition 4.13, p.24

import Mathlib
import Definitions.Def_ScalarMultiRisk_priceSetAt

open MeasureTheory

namespace ScalarMultiRisk

/-- **The set `𝒮*`.** arXiv:1807.10694v5, Definition 4.13, p.24: `𝒮* := ⋂_{t ≥ 0} 𝒮_t`. -/
def priceSetStar {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} [NeZero d] (A : Market Ω T d)
    (ρ : Fin (T + 1) → (Ω → Fin d → ℝ) → Ω → ℝ) : Set (Fin (T + 1) → Ω → Fin d → ℝ) :=
  ⋂ t, priceSetAt A ρ t

end ScalarMultiRisk


