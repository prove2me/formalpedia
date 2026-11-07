-- Prove2me | Definitions.Def_ReplicableOL_E2
-- name    : ReplicableOL_E2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:47:35.347018+00:00
-- url     : https://prove2.me/theorems/c24aa74d-3dbc-4e37-b3dd-dd0a2c8a0aa4
-- title:
--   Expectation over $(\theta,S,S')$
-- statement:
--   The expectation $\mathbb E_{\theta,S,S'}[f(\theta,S,S')]$ for two conditionally independent runs of the data given $\theta$.
--
--   **Formalization Note** A finite double sum over bits under an integral against the prior. A probability is `E2` of an `if … then 1 else 0`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 4.1, p.15

import Mathlib
import Definitions.Def_ReplicableOL_Bits
import Definitions.Def_ReplicableOL_seqWeight
import Definitions.Def_ReplicableOL_epochPrior
open MeasureTheory ProbabilityTheory

namespace ReplicableOL

/-- **Expectation over $(\theta,S,S')$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 4.1, p.15. "Four data sequences S, S′, S″, S‴ are conditionally i.i.d. given θ"; this is the expectation over `θ` and the two real runs.

**Formalization Note.** A finite double sum over bits under an integral against the prior. A probability is `E2` of an `if … then 1 else 0`. -/
noncomputable def E2 {k L : ℕ} (Δ : ℝ) (f : (Fin k → ℝ) → Bits k L → Bits k L → ℝ) : ℝ :=
  ∫ θ, ∑ S : Bits k L, ∑ S' : Bits k L, seqWeight θ S * seqWeight θ S' * f θ S S' ∂(epochPrior k Δ)

end ReplicableOL


