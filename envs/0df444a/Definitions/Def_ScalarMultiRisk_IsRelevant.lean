-- Prove2me | Definitions.Def_ScalarMultiRisk_IsRelevant
-- name    : ScalarMultiRisk_IsRelevant
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:16:03.465901+00:00
-- url     : https://prove2.me/theorems/a9162f03-8875-4adb-996b-3dd89f5783c7
-- title:
--   Definition 3.15 — relevance
-- statement:
--   A risk measure $\rho_t$ is **relevant** if
--
--   $$\mathbb P\big(\rho_t(-\epsilon 1_D e_1)>\rho_t(0)\big)>0$$
--
--   for every $\epsilon>0$ and every $D\in\mathcal F$ with $\mathbb P(D)>0$. Relevance makes the dual representation run over equivalent measures.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Definition 3.15, p.15

import Mathlib
import Definitions.Def_ScalarMultiRisk_FilteredSpace

open MeasureTheory

namespace ScalarMultiRisk

/-- **Relevance.** arXiv:1807.10694v5, Definition 3.15, p.15:
`ℙ(ρ_t(−ε 1_D e₁) > ρ_t(0)) > 0` for every `ε > 0` and every `D ∈ F` with `ℙ(D) > 0`. -/
def IsRelevant {Ω : Type*} [MeasurableSpace Ω] {T : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : FilteredSpace Ω T) (e : E) (r : (Ω → E) → Ω → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ D : Set Ω, MeasurableSet D → 0 < B.P D →
    0 < B.P {ω | r 0 ω < r (fun ω' => (-ε * D.indicator 1 ω') • e) ω}

end ScalarMultiRisk


