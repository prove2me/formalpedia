-- Prove2me | Definitions.Def_ScalarMultiRisk_StandingAssumptions
-- name    : ScalarMultiRisk_StandingAssumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:20:13.607004+00:00
-- url     : https://prove2.me/theorems/9bcfd867-c11e-45fb-bf36-9225aa64a30e
-- title:
--   Assumptions 3.3 and 4.1 — the standing assumptions on $(\rho_t)$
-- statement:
--   For every time $t$, $\rho_t$ is a scalarized conditional convex risk measure on $L^\infty(\mathbb R^d)$ that is $\mathbb K_t$-compatible, relevant, and has the Fatou property. These assumptions hold throughout §4, so they are hypotheses of every result of the mission.
--
--   **Formalization Note** The paper starts from a set-valued risk measure $R_t$, with $\rho_t$ given by (3.1). By Theorem 3.2, $R_t(X)=(\rho_t(X)+L^\infty_t(\mathbb R_+))e_1$, so the assumption can be stated through $\rho_t$ alone, and $A_t=\{X\mid\rho_t(X)\le0\text{ a.s.}\}$. The conditions on the cones are part of the market.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Assumption 3.3, p.8, and Assumption 4.1, p.17

import Mathlib
import Definitions.Def_ScalarMultiRisk_Market
import Definitions.Def_QKPSDP_e1
import Definitions.Def_ScalarMultiRisk_IsScalarRisk
import Definitions.Def_ScalarMultiRisk_IsKCompatible
import Definitions.Def_ScalarMultiRisk_HasFatou
import Definitions.Def_ScalarMultiRisk_IsRelevant

open MeasureTheory

namespace ScalarMultiRisk

/-- **The standing assumptions.** arXiv:1807.10694v5, Assumption 3.3, p.8, and Assumption 4.1,
p.17: each `ρ_t` is a scalarized conditional convex risk measure (Definition 3.1), `𝕂_t`-compatible
for the solvency cones of the market, relevant (Definition 3.15), with the Fatou property
(Definition 3.5).

**Formalization Note.** Assumption 3.3 starts from a set-valued `R_t` with `ρ_t` defined by (3.1)
and `A_t = {X | 0 ∈ R_t(X)}`. By the converse part of Theorem 3.2, `R_t(X) = (ρ_t(X) + L∞_t(ℝ₊))e₁`,
and conversely this formula turns a `𝕂_t`-compatible `ρ_t` into such an `R_t`. So the assumption is
stated through `ρ_t`, with `A_t = {X | ρ_t(X) ≤ 0 a.s.}` (`riskAcceptance`). No set-valued object
is formalized. The conditions on the cones are in `Market`. -/
structure StandingAssumptions {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} [NeZero d]
    (A : Market Ω T d) (ρ : Fin (T + 1) → (Ω → Fin d → ℝ) → Ω → ℝ) : Prop where
  /-- Each `ρ_t` is a scalarized conditional convex risk measure. -/
  risk : ∀ t, IsScalarRisk A.toFilteredSpace t (QKPSDP.e1 d) (ρ t)
  /-- Each `ρ_t` is `𝕂_t`-compatible. -/
  compatible : ∀ t, IsKCompatible A t (ρ t)
  /-- Each `ρ_t` has the Fatou property. -/
  fatou : ∀ t, HasFatou A.toFilteredSpace (ρ t)
  /-- Each `ρ_t` is relevant. -/
  relevant : ∀ t, IsRelevant A.toFilteredSpace (QKPSDP.e1 d) (ρ t)

end ScalarMultiRisk


