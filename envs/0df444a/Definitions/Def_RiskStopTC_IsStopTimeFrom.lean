-- Prove2me | Definitions.Def_RiskStopTC_IsStopTimeFrom
-- name    : RiskStopTC_IsStopTimeFrom
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:34:23.981414+00:00
-- url     : https://prove2.me/theorems/88c01dd9-7ab7-4006-811c-478dcac43bb7
-- title:
--   The stopping times $\mathfrak T_m=\{\tau\in\mathfrak T:\tau\ge m\}$
-- statement:
--   A **stopping time** is a random variable $\tau:\Omega\to\{0,\dots,T\}$ with $\{\tau=t\}\in\mathcal F_t$ for $t=0,\dots,T$; $\mathfrak T$ is the set of stopping times. For $m\in\{0,\dots,T\}$,
--   $$\mathfrak T_m:=\{\tau\in\mathfrak T:\ \tau\ge m\}.$$
--
--   $\mathfrak T_m$ is the feasible set of the stopping problem (5.15).
--
--   **Formalization Note** Uses the published `MultiperiodRisk.Bellman.IsBddStoppingTime ℱ T τ` (Mathlib's `IsStoppingTime` with values in `WithTop ℕ`, and $\tau\le T$ everywhere); in discrete time this is equivalent to $\{\tau=t\}\in\mathcal F_t$ for all $t$. The bound $m\le\tau$ holds everywhere, as on p.20.
-- source:
--   Pichler, Liu & Shapiro, Risk averse stochastic programming: time consistency and optimal stopping, arXiv:1808.10807v3, pp.3–4 (stopping times, 𝔗); p.20 (𝔗_m)

import Mathlib
import Definitions.Def_MultiperiodRisk_Bellman_TestSet

namespace RiskStopTC

open MeasureTheory

/-- **The stopping times `𝔗_m`.** Pichler, Liu & Shapiro, arXiv:1808.10807v3, pp.3–4: "a stopping
time, adapted to the filtration F, is a random variable τ : Ω → {0, . . . , T} such that
{ω ∈ Ω : τ(ω) = t} ∈ Ft for t = 0, . . . , T", and p.20: "𝔗m := {τ ∈ 𝔗 : τ ≥ m}".

`IsStopTimeFrom ℱ T m τ`: `τ` is a stopping time with `m ≤ τ ≤ T` everywhere.

**Formalization Note.** Uses the published `MultiperiodRisk.Bellman.IsBddStoppingTime ℱ T τ`
(Mathlib's `IsStoppingTime ℱ τ` with values in `WithTop ℕ`, and `τ ≤ T` everywhere). In discrete
time `{τ ≤ t} ∈ F_t` for all `t` is equivalent to `{τ = t} ∈ F_t` for all `t`. -/
def IsStopTimeFrom {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ) (T m : ℕ)
    (τ : Ω → WithTop ℕ) : Prop :=
  MultiperiodRisk.Bellman.IsBddStoppingTime ℱ T τ ∧ ∀ ω, (m : WithTop ℕ) ≤ τ ω

end RiskStopTC


