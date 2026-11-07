-- Prove2me | Definitions.Def_ReplicableOL_epochPrior
-- name    : ReplicableOL_epochPrior
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:50.55124+00:00
-- url     : https://prove2.me/theorems/6f1fef74-7f2a-4224-a898-fc97eb85849e
-- title:
--   Prior on $\theta=(\mu_1,\dots,\mu_k)$
-- statement:
--   The prior on the vector of epoch means $\theta=(\mu_1,\dots,\mu_k)$, whose coordinates are i.i.d. uniform on $[-\Delta,\Delta]$.
--
--   **Formalization Note** A product measure on `Fin k → ℝ`, with 0-based epochs.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.1, p.7

import Mathlib
import Definitions.Def_ReplicableOL_uniformPrior
open MeasureTheory ProbabilityTheory

namespace ReplicableOL

/-- **Prior on $\theta=(\mu_1,\dots,\mu_k)$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.1, p.7. `θ = (μ_1, …, μ_k)` with `μ_j` i.i.d. uniform on `[−Δ, Δ]`.

**Formalization Note.** A product measure on `Fin k → ℝ`, with 0-based epochs. -/
noncomputable def epochPrior (k : ℕ) (Δ : ℝ) : Measure (Fin k → ℝ) :=
  Measure.pi fun _ : Fin k => uniformPrior Δ

end ReplicableOL


