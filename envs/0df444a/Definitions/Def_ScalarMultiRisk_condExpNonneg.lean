-- Prove2me | Definitions.Def_ScalarMultiRisk_condExpNonneg
-- name    : ScalarMultiRisk_condExpNonneg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:16:17.762749+00:00
-- url     : https://prove2.me/theorems/97748976-b888-4b8a-99c5-d041706bac8a
-- title:
--   Conditional expectation of a nonnegative extended random variable
-- statement:
--   $\mathbb E^{\mathbb Q}[Y\mid\mathcal F_t]$ for a random variable $Y$ with values in $[0,\infty]$: the a.s. unique $\mathcal F_t$-measurable $[0,\infty]$-valued $W$ with $\int_B W\,d\mathbb Q=\int_B Y\,d\mathbb Q$ for all $B\in\mathcal F_t$. It is what $\mathbb E^{\mathbb Q}[\beta_s(\mathbb Q,S)\mid\mathcal F_t]$ means when $\beta_s$ can be infinite.
--
--   **Formalization Note** This is Mathlib's conditional Lebesgue expectation `condLExp`. The real conditional expectation would return $0$ on non-integrable functions, which would change the statement.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Theorem 4.15(4), p.24

import Mathlib
import Definitions.Def_ScalarMultiRisk_FilteredSpace

open MeasureTheory

namespace ScalarMultiRisk

/-- **Conditional expectation of a nonnegative extended random variable.** The term
`𝔼^ℚ[β_s(ℚ,S) | F_t]` of arXiv:1807.10694v5, Theorem 4.15(4), p.24.

**Formalization Note.** `β_s(ℚ,S)` can be `+∞` on a non-null set, and Mathlib's real `condExp`
is `0` on non-integrable functions, so it cannot be used. This is Mathlib's `condLExp`, the
conditional Lebesgue expectation of the `ℝ≥0∞`-valued function `Y.toENNReal`, read back in
`EReal`. It is applied to `Y ≥ 0` a.s. only: under normalization `β_s(ℚ,S) ≥ −π^S_s(0) = 0`,
so `toENNReal` does not change `Y`. -/
noncomputable def condExpNonneg {Ω : Type*} [MeasurableSpace Ω] {T : ℕ}
    (B : FilteredSpace Ω T) (Q : Measure Ω) (t : Fin (T + 1)) (Y : Ω → EReal) : Ω → EReal :=
  fun ω => ((condLExp (B.F t) Q (fun ω' => (Y ω').toENNReal) ω : ENNReal) : EReal)

end ScalarMultiRisk


