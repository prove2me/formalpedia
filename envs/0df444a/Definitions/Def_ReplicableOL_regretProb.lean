-- Prove2me | Definitions.Def_ReplicableOL_regretProb
-- name    : ReplicableOL_regretProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:47:23.295386+00:00
-- url     : https://prove2.me/theorems/dac262df-c9fa-48af-9297-320d547a8334
-- title:
--   The probability $\mathbb P_{\theta,S,R}[\mathrm{Reg}_T\ge b]$
-- statement:
--   The joint probability, over $\theta\sim U[-\Delta,\Delta]^k$, $S\sim P_\theta$ and an independent seed $R\sim P_R$, that the realized regret of a fixed learner is at least $b$.
--
--   **Formalization Note** The joint law of `(θ, S, R)` is written as an iterated `lintegral` in `ℝ≥0∞`, with `k = T / L`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Theorem 1 (precise form), p.9

import Mathlib
import Definitions.Def_ReplicableOL_regret
import Definitions.Def_ReplicableOL_lawP
import Definitions.Def_ReplicableOL_epochPrior
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ReplicableOL

/-- **The probability $\mathbb P_{\theta,S,R}[\mathrm{Reg}_T\ge b]$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Theorem 1 (precise form), p.9. `P_{θ,S,R}[Reg_T ≥ b]`: the learner is fixed first, then `θ, S, R` are drawn (H5), and `R` is independent of `θ, S` (H2).

**Formalization Note.** The joint law of `(θ, S, R)` is written as an iterated `lintegral` in `ℝ≥0∞`, with `k = T / L`. -/
noncomputable def regretProb {T : ℕ} {R : Type*} [MeasurableSpace R] (𝓛 : Learner 2 T R)
    (PR : Measure R) (L : ℕ) (Δ b : ℝ) : ℝ≥0∞ :=
  ∫⁻ θ, ∫⁻ r, lawP T L θ {S | b ≤ regret 𝓛 S r} ∂PR ∂(epochPrior (T / L) Δ)

end ReplicableOL


