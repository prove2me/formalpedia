-- Prove2me | Definitions.Def_ReplicableOL_E1
-- name    : ReplicableOL_E1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:47:44.589574+00:00
-- url     : https://prove2.me/theorems/20c930d7-82d9-4de2-8733-4e28baa64d45
-- title:
--   Expectation over $(\theta,S)$
-- statement:
--   The expectation $\mathbb E_{\theta,S}[f(\theta,S)]$ over the epoch means and the bits of Construction C, written as an integral over the prior of a finite sum over block sequences.
--
--   **Formalization Note** A finite sum over bits under an integral against the prior. A probability is `E1` of an `if … then 1 else 0`. The integrands used in the mission are bounded on the prior's support, and the verification file proves integrability for bounded measurable integrands.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 3.2, p.11

import Mathlib
import Definitions.Def_ReplicableOL_Bits
import Definitions.Def_ReplicableOL_seqWeight
import Definitions.Def_ReplicableOL_epochPrior
open MeasureTheory ProbabilityTheory

namespace ReplicableOL

/-- **Expectation over $(\theta,S)$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 3.2, p.11. "E and P are over (θ, S) at this seed".

**Formalization Note.** A finite sum over bits under an integral against the prior. A probability is `E1` of an `if … then 1 else 0`. The integrands used in the mission are bounded on the prior's support, and the verification file proves integrability for bounded measurable integrands. -/
noncomputable def E1 {k L : ℕ} (Δ : ℝ) (f : (Fin k → ℝ) → Bits k L → ℝ) : ℝ :=
  ∫ θ, ∑ S : Bits k L, seqWeight θ S * f θ S ∂(epochPrior k Δ)

end ReplicableOL


