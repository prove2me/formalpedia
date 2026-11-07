-- Prove2me | Definitions.Def_ReplicableOL_avgWeight
-- name    : ReplicableOL_avgWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:50.062687+00:00
-- url     : https://prove2.me/theorems/d6294456-6c10-4eca-8408-e24de05abadd
-- title:
--   Mixed block law $\bar\nu$
-- statement:
--   The probability of a block under the mixture $\bar\nu=\frac1{2\Delta}\int_{-\Delta}^{\Delta}\nu_\mu\,d\mu$, that is, the marginal law of one block.
--
--   **Formalization Note** An integral of a polynomial against the uniform law, so it is genuine.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Lemma 4.1(d), p.15

import Mathlib
import Definitions.Def_ReplicableOL_blockWeight
import Definitions.Def_ReplicableOL_uniformPrior
open MeasureTheory ProbabilityTheory

namespace ReplicableOL

/-- **Mixed block law $\bar\nu$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Lemma 4.1(d), p.15. `ν̄ := (1/(2Δ)) ∫_{−Δ}^{Δ} ν_μ dμ`.

**Formalization Note.** An integral of a polynomial against the uniform law, so it is genuine. -/
noncomputable def avgWeight {L : ℕ} (Δ : ℝ) (s : Block L) : ℝ :=
  ∫ μ, blockWeight μ s ∂(uniformPrior Δ)

end ReplicableOL


