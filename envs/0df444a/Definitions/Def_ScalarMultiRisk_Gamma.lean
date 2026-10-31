-- Prove2me | Definitions.Def_ScalarMultiRisk_Gamma
-- name    : ScalarMultiRisk_Gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:08.103743+00:00
-- url     : https://prove2.me/theorems/af9adc95-6044-476a-9924-ba4d7798b12b
-- title:
--   The set $\Gamma_t(S_t)$
-- statement:
--   $\Gamma_t(S_t)=\{Z\in L^\infty_t(\mathbb R^d)\mid S_t^{\mathsf T}Z\ge0\text{ a.s.}\}$ is the set of $\mathcal F_t$-measurable bounded portfolios of nonnegative value at prices $S_t$.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Definition 4.3, p.18

import Mathlib
import Definitions.Def_ScalarMultiRisk_LinftyFull
import Definitions.Def_ScalarMultiRisk_payoff

open MeasureTheory

namespace ScalarMultiRisk

/-- **The set `Γ_t(S_t)`.** arXiv:1807.10694v5, Definition 4.3, p.18:
`Γ_t(S_t) := {Z ∈ L∞_t(ℝ^d) | S_t^T Z ≥ 0 a.s.}`. -/
def Gamma {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} (B : FilteredSpace Ω T)
    (S : Fin (T + 1) → Ω → Fin d → ℝ) (t : Fin (T + 1)) : Set (Ω → Fin d → ℝ) :=
  {Z ∈ LinftyFull B t | ∀ᵐ ω ∂B.P, 0 ≤ payoff (S t) Z ω}

end ScalarMultiRisk


