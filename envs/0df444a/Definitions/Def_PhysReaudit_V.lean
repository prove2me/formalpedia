-- Prove2me | Definitions.Def_PhysReaudit_V
-- name    : PhysReaudit_V
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:48:35.033338+00:00
-- url     : https://prove2.me/theorems/a2e1318e-b555-4138-858e-4e568366bcfb
-- title:
--   Minimax re-auditing cost $V_\delta$
-- statement:
--   Fix an old-data law $\nu_0$ on a measurable space $W_0$. A rule may use the old transcript $w_0\sim\nu_0$ together with private randomness $u\sim\rho$ on any measurable space $U$, independent of $w_0$, and may abort and restart. The **minimax re-auditing cost** is
--
--   $$
--   V_\delta=\inf_{(U,\rho,R)}\ \sup_{q\in[0,q_0]}\mathbb E_qC ,
--   $$
--
--   the infimum over all such $(U,\rho,R)$ for which $R$ (with side law $\nu_0\otimes\rho$) is $\delta$-sound and $\varepsilon$-complete, of the worst expected physical cost over the good parameters $q\in[0,q_0]$, $q_0=(b-\varepsilon)/(\kappa a^d)$.
--
--   **Formalization Note** Valued in $[0,\infty]$; an empty class of rules would give $+\infty$. The randomness space ranges over every `U : Type`. The old-data law is fixed by the environment and is not chosen by the auditor.
-- source:
--   Q. Li, When Can Physical Evidence Survive a World-Model Update? Finite-cost re-auditing and reusable policy certificates, review revision of 3 November 2026 (STOC 2027 submission, sha256 a20c437b34115b84982339e9a6fa319cb3a66f66d9d4c474465cbb954c79093d), Theorem 4, p.3 (PDF p.4): "Let Vδ be the infimum, over δ-sound and ε-complete rules, of sup_{q≤q0} EqC."

import Mathlib
import Definitions.Def_PhysReaudit_Delta
import Definitions.Def_PhysReaudit_Rule
import Definitions.Def_PhysReaudit_run
import Definitions.Def_PhysReaudit_lawQ
import Definitions.Def_PhysReaudit_IsSound

open MeasureTheory

namespace PhysReaudit

/-- The minimax re-auditing cost `V_δ` (Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), Theorem 4, p.3 (PDF p.4)): "the infimum, over δ-sound and
ε-complete rules, of sup_{q≤q₀} E_q C".

The old transcript is a random variable on `W₀` with law `ν₀` (the same for every target parameter). A rule
may in addition use private randomness `u ∈ U` with an arbitrary law `ρ`, independent of the old data, and
may abort and restart. `V ν₀ a d b κ ε δ` is the infimum, over all such `(U, ρ, R)` with `R` δ-sound and
ε-complete, of `⨆_{q ∈ [0, q₀]} E_q C`.

**Formalization Note** Valued in `ℝ≥0∞` (an empty class gives `⊤`). The randomness space ranges over
`U : Type` with any measurable structure; the old data law `ν₀` is fixed by the environment, not chosen by
the auditor. -/
noncomputable def V {W₀ : Type} [MeasurableSpace W₀] (ν₀ : Measure W₀) (a : ℝ) (d : ℕ)
    (b κ ε δ : ℝ) : ENNReal :=
  ⨅ (U : Type) (_mU : MeasurableSpace U) (ρ : Measure U) (_ : IsProbabilityMeasure ρ)
    (R : Rule (W₀ × U))
    (_ : IsSound R (ν₀.prod ρ) a d b κ δ ∧ IsComplete R (ν₀.prod ρ) a d b κ ε δ),
    ⨆ q ∈ Set.Icc (0 : ℝ) (q0 a d b κ ε), expCost R (ν₀.prod ρ) a d q

end PhysReaudit


