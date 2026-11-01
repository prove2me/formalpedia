-- Prove2me | Definitions.Def_RiskStopTC_optValue
-- name    : RiskStopTC_optValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:36:26.245965+00:00
-- url     : https://prove2.me/theorems/4f7f7838-8012-448c-ab60-1752841f9b91
-- title:
--   The optimal value $\mathfrak v_m$ of the stopping problem (5.15)
-- statement:
--   For $m\in\{0,\dots,T\}$, $\mathfrak v_m$ is the optimal value of (5.15):
--   $$\mathfrak v_m=\sup\{\rho_{0,T}(Z_\tau):\ \tau\in\mathfrak T_m\}.$$
--
--   Clause (iv) of Theorem 5.6 computes it as $\rho_{0,m}(E_m)$.
--
--   **Formalization Note** A real supremum (`sSup`). Clause (ii) of Theorem 5.6 states that the set has a greatest element, so the default value of `sSup` on an empty or unbounded set is never used.
-- source:
--   Pichler, Liu & Shapiro, Risk averse stochastic programming: time consistency and optimal stopping, arXiv:1808.10807v3, p.20 ("Denote by 𝔳m the optimal value of the problem (5.15)")

import Mathlib
import Definitions.Def_RiskStopTC_stopValue
import Definitions.Def_RiskStopTC_IsStopTimeFrom

namespace RiskStopTC

open MeasureTheory

/-- **The optimal value `𝔳_m` of (5.15).** Pichler, Liu & Shapiro, arXiv:1808.10807v3, p.20:
"Denote by 𝔳m the optimal value of the problem (5.15)", where (5.15) is
"max_{τ∈𝔗m} ρ0,T(Zτ)".

`optValue ℱ P ϱ Z T m = sup {ρ_{0,T}(Z_τ) : τ ∈ 𝔗_m}`.

**Formalization Note.** A real `sSup`. It is the true optimal value whenever the set has a greatest
element, which is clause (ii) of Theorem 5.6 (stated there as `IsGreatest`), so the junk value of
`sSup` on an empty or unbounded set is never used. -/
noncomputable def optValue {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ)
    (P : Measure[mΩ] Ω) (ϱ : ℕ → (Ω → ℝ) → Ω → ℝ) (Z : ℕ → Ω → ℝ) (T m : ℕ) : ℝ :=
  sSup (stopValue P ϱ Z T '' {τ | IsStopTimeFrom ℱ T m τ})

end RiskStopTC


