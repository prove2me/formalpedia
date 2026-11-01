-- Prove2me | Definitions.Def_RiskStopTC_stoppedRV
-- name    : RiskStopTC_stoppedRV
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:34:12.506393+00:00
-- url     : https://prove2.me/theorems/bd553506-723c-40a5-bfe4-597f09d73512
-- title:
--   The stopped reward $Z_\tau=\sum_{t=0}^T\mathbb 1_{\{\tau=t\}}Z_t$ (2.4)
-- statement:
--   For a process $Z_0,\dots,Z_T$ and a random time $\tau$ with values in $\{0,\dots,T\}$, the **stopped reward** is
--   $$Z_\tau=\sum_{t=0}^T\mathbb 1_{\{\tau=t\}}Z_t,$$
--   so that $Z_\tau(\omega)=Z_{\tau(\omega)}(\omega)$.
--
--   It is the argument of the risk functional in the stopping problem (5.15).
--
--   **Formalization Note** Stopping times take values in `WithTop ℕ` (Mathlib's convention). The sum runs over $t=0,\dots,T$; a value $\tau(\omega)>T$ (never occurring for the stopping times of the mission) would give $0$.
-- source:
--   Pichler, Liu & Shapiro, Risk averse stochastic programming: time consistency and optimal stopping, arXiv:1808.10807v3, equation (2.4), p.5

import Mathlib

namespace RiskStopTC

/-- **The stopped reward (2.4).** Pichler, Liu & Shapiro, arXiv:1808.10807v3, (2.4), p.5:
"Zτ = ∑_{t=0}^T 1{τ=t} Zτ = ∑_{t=0}^T 1{τ=t} Zt."

`stoppedRV Z τ T ω = ∑_{t=0}^{T} 1{τ = t}(ω) Z_t(ω)`.

**Formalization Note.** Stopping times take values in `WithTop ℕ` (Mathlib's convention); every
stopping time of the mission satisfies `τ ≤ T` everywhere, and then this is `Z_{τ(ω)}(ω)`. -/
noncomputable def stoppedRV {Ω : Type*} (Z : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ) (T : ℕ) :
    Ω → ℝ :=
  fun ω => ∑ t ∈ Finset.range (T + 1), ({ω' | τ ω' = (t : WithTop ℕ)}).indicator (Z t) ω

end RiskStopTC


