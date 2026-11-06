-- Prove2me | Definitions.Def_IAFTRL_IsCorrupted
-- name    : IAFTRL_IsCorrupted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:52.477272+00:00
-- url     : https://prove2.me/theorems/9c000d34-42d0-4b26-aba8-0fdc0b6824c4
-- title:
--   Corrupted stochastic regime with budget $C$
-- statement:
--   A run is in the **corrupted stochastic regime** with fixed loss vector $\theta$ and budget $C$ over $T$ rounds if
--   1. $\|\theta\|_{\mathcal A}\le1$;
--   2. almost surely,
--   $$
--   \sum_{t\le T}\kappa_t\le C,\qquad \kappa_t=\|c^{\mathrm{vec}}_t\|_{\mathcal A},\quad c^{\mathrm{vec}}_t=\theta_t-\theta .
--   $$
--
--   The corruption level $C$ is deterministic and unknown to the learner; $C=0$ is the stochastic regime.
--
--   **Formalization Note** The condition $\|\theta\|_{\mathcal A}\le1$ is the stochastic regime's; the paper uses it in the corrupted regime as $0\le\kappa_t\le2$. The sign condition $C\ge0$ is a separate hypothesis of each theorem.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Section 1.1, pp.5–6

import Mathlib
import Definitions.Def_IAFTRL_actionNorm
import Definitions.Def_IAFTRL_Run

namespace IAFTRL

open MeasureTheory

/-- **The corrupted stochastic regime with budget `C`.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Section 1.1, pp.5–6: "In the
stochastic regime, `θ_t = θ` for all `t ∈ [T]`, where `θ` is an unknown fixed loss vector with
`‖θ‖_𝒜 ≤ 1`" and "In this regime, there exists some fixed yet unknown `θ` so that the actual loss
vector `θ_t` is `θ_t = θ + c^{vec}_t`, where `κ_t = ‖c^{vec}_t‖_𝒜`. Let `C ≥ 0` be a deterministic
corruption level, unknown to the learner, such that `Σ_{t≤T} κ_t ≤ C` almost surely."

`IsCorrupted P arms θ C T R` says `‖θ‖_𝒜 ≤ 1` and, almost surely, `Σ_{t<T} ‖θ_t − θ‖_𝒜 ≤ C`.

**Formalization Note.** `c^{vec}_t := θ_t − θ`. The condition `‖θ‖_𝒜 ≤ 1` is the stochastic
regime's (p.5); the paper uses it in the corrupted regime as `0 ≤ κ_t ≤ 2` (p.86). `C ≥ 0` is a
separate hypothesis of each theorem. -/
def IsCorrupted {d K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (arms : Fin K → Fin d → ℝ) (θ : Fin d → ℝ) (C : ℝ) (T : ℕ) (R : Run d K Ω) : Prop :=
  actionNorm arms θ ≤ 1 ∧
    ∀ᵐ ω ∂P, ∑ t ∈ Finset.range T, actionNorm arms (R.θs t ω - θ) ≤ C

end IAFTRL


