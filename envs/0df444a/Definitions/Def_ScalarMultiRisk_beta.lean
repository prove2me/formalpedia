-- Prove2me | Definitions.Def_ScalarMultiRisk_beta
-- name    : ScalarMultiRisk_beta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:19:58.462702+00:00
-- url     : https://prove2.me/theorems/03cb5ee5-a43d-4df0-aa1b-42446702613b
-- title:
--   The penalty $\beta_t(\mathbb Q,S)$
-- statement:
--   The **penalty** of a pair $(\mathbb Q,S)$ is
--
--   $$\beta_t(\mathbb Q,S)=\operatorname*{ess\,sup}_{Z\in A_t}-\mathbb E^{\mathbb Q}[S_T^{\mathsf T}Z\mid\mathcal F_t],$$
--
--   with values in $[-\infty,\infty]$.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Theorem 3.8, p.11

import Mathlib
import Definitions.Def_ScalarMultiRisk_riskAcceptance
import Definitions.Def_ScalarMultiRisk_essSupE
import Definitions.Def_ScalarMultiRisk_payoff

open MeasureTheory

namespace ScalarMultiRisk

/-- **The penalty `β_t(ℚ,S)`.** arXiv:1807.10694v5, Theorem 3.8, p.11:
`β_t(ℚ,S) = ess sup_{Z ∈ A_t} −𝔼^ℚ[S_T^T Z | F_t]`.

**Formalization Note.** `β_t` can be `+∞`, so it is `EReal`-valued. The paper's a.s. version of
`𝔼^ℚ` is Mathlib's `ℚ[·|F t]` for `ℚ ∼ ℙ`, the only case used. `S_T^T Z` is bounded, so the
conditional expectation has no junk value. -/
noncomputable def beta {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} (A : Market Ω T d)
    (ρ : Fin (T + 1) → (Ω → Fin d → ℝ) → Ω → ℝ) (t : Fin (T + 1)) (Q : Measure Ω)
    (S : Fin (T + 1) → Ω → Fin d → ℝ) : Ω → EReal :=
  essSupE A.P fun Z : riskAcceptance A ρ t =>
    fun ω => ((-(Q[payoff (S (Fin.last T)) Z.1 | A.F t] ω) : ℝ) : EReal)

end ScalarMultiRisk


