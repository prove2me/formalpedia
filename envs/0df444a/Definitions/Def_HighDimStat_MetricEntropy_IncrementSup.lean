-- Prove2me | Definitions.Def_HighDimStat_MetricEntropy_IncrementSup
-- name    : HighDimStat_MetricEntropy_IncrementSup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:00:12.340272+00:00
-- url     : https://prove2.me/theorems/803a97a1-6055-4399-80a6-159ab6895a0f
-- title:
--   The full supremum of process increments over T x T
-- statement:
--   The full increment supremum $\sup_{\theta,\theta'\in T}(X_\theta - X_{\theta'})$ appearing on
--   the left-hand side of both Proposition 5.17 (Eq. (5.33)) and Theorem 5.22 (Eq. (5.46)), as a
--   function of the outcome $\omega$.
--
--   $$
--   \mathrm{IncrementSup}(\omega) \;:=\; \sup_{\theta,\theta'\in T} \big(X_\theta(\omega) - X_{\theta'}(\omega)\big).
--   $$
--
--   **Formalization Note** Realized as `⨆` over the finite type `T × T`; well-defined as the true
--   maximum (not Mathlib's junk value `0`) since `T × T` is finite.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 135 (PDF p. 155), Eq. (5.33)

import Mathlib

namespace HighDimStat.MetricEntropy

/-- The full increment supremum `sup_{θ,θ' ∈ T} (Xθ(ω) - Xθ'(ω))` appearing on the left-hand side
of Wainwright, *High-Dimensional Statistics* (2019), Proposition 5.17 and Theorem 5.22 (Eqs.
(5.33), (5.46)). Realized as `⨆` over the finite type `T × T`; well-defined (not the junk value
`0` for an unbounded set) since `T × T` is finite, and equal to the true maximum whenever `T` is
nonempty. -/
noncomputable def IncrementSup {T Ω : Type*} [Fintype T] (X : T → Ω → ℝ) (ω : Ω) : ℝ :=
  ⨆ p : T × T, (X p.1 ω - X p.2 ω)

end HighDimStat.MetricEntropy


