-- Prove2me | Definitions.Def_ScalarMultiRisk_betaStep
-- name    : ScalarMultiRisk_betaStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:27:05.977237+00:00
-- url     : https://prove2.me/theorems/3afcbe9d-4dcb-4ecf-b9e7-5251bef0e0ef
-- title:
--   The stepped penalty $\beta^S_{t,s}(\mathbb Q)$
-- statement:
--   For $\mathbb Q\in\mathcal Q^e(S)$,
--
--   $$\beta^S_{t,s}(\mathbb Q)=\operatorname*{ess\,sup}_{X\in A^\pi_{t,s}}-\mathbb E^{\mathbb Q}[S_s^{\mathsf T}X\mid\mathcal F_t].$$
--
--   **Formalization Note** The formula is taken as the definition. That it is the minimal penalty of $\phi^S_{t,s}$ is part of Corollary 4.11.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Corollary 4.11(2), p.23

import Mathlib
import Definitions.Def_ScalarMultiRisk_ApiStep
import Definitions.Def_ScalarMultiRisk_essSupE
import Definitions.Def_ScalarMultiRisk_payoff

open MeasureTheory

namespace ScalarMultiRisk

/-- **The stepped penalty `β^S_{t,s}(ℚ)`.** arXiv:1807.10694v5, Corollary 4.11(2), p.23:
`β^S_{t,s}(ℚ) = ess sup_{X ∈ A^π_{t,s}} −𝔼^ℚ[S_s^T X | F_t]`.

**Formalization Note.** The corollary asserts that this formula is the minimal penalty of the
stepped risk measure `φ^S_{t,s}`. Here it is the definition, and that assertion is a statement
of the corollary about the ess sup over `A^φ_{t,s}`. -/
noncomputable def betaStep {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} (A : Market Ω T d)
    (ρ : Fin (T + 1) → (Ω → Fin d → ℝ) → Ω → ℝ) (S : Fin (T + 1) → Ω → Fin d → ℝ)
    (t s : Fin (T + 1)) (Q : Measure Ω) : Ω → EReal :=
  essSupE A.P fun X : ApiStep A ρ S t s =>
    fun ω => ((-(Q[payoff (S s) X.1 | A.F t] ω) : ℝ) : EReal)

end ScalarMultiRisk


