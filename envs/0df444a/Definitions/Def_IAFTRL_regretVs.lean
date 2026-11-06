-- Prove2me | Definitions.Def_IAFTRL_regretVs
-- name    : IAFTRL_regretVs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:39.167203+00:00
-- url     : https://prove2.me/theorems/58be73ed-f0ed-4677-a123-caabe3d6589e
-- title:
--   Regret against a fixed comparator $\mathrm{Reg}_T(u)$
-- statement:
--   The **regret against a fixed comparator action** $u\in\mathcal A$ over $T$ rounds is
--   $$
--   \mathrm{Reg}_T(u)=\mathbb E\Big[\sum_{t=1}^T(A_t-u)^\top\theta_t\Big],
--   $$
--   the expectation being over the learner and the environment. The pseudo-regret is $\mathrm{Reg}_T=\max_{u\in\mathcal A}\mathrm{Reg}_T(u)$, with the maximum outside the expectation.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Section 1.1, p.5; Appendix J.1, p.204

import Mathlib
import Definitions.Def_IAFTRL_Run

namespace IAFTRL

open Matrix MeasureTheory

/-- **Regret against a fixed comparator, `Reg_T(u)`.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Section 1.1, p.5:
"`Reg_T := sup_{u∈𝒜} Reg_T(u)`, where `Reg_T(u) = E[Σ_{t=1}^T (A_t − u)^⊤θ_t]`"; Appendix J.1, p.204: "All
guarantees concern expectation against a fixed comparator, with any final supremum outside
expectation."

`regretVs P arms T R u = ∫ Σ_{t<T} (a_{A_t} − a_u)^⊤θ_t dP` for the comparator action `a_u = arms u`.
The pseudo-regret `Reg_T` is the maximum over `u` of these numbers; a bound on every
`regretVs … u` is a bound on `Reg_T`. -/
noncomputable def regretVs {d K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (arms : Fin K → Fin d → ℝ) (T : ℕ) (R : Run d K Ω) (u : Fin K) : ℝ :=
  ∫ ω, ∑ t ∈ Finset.range T, (arms (R.A t ω) - arms u) ⬝ᵥ R.θs t ω ∂P

end IAFTRL


