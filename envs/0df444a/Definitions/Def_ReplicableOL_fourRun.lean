-- Prove2me | Definitions.Def_ReplicableOL_fourRun
-- name    : ReplicableOL_fourRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:48:31.344028+00:00
-- url     : https://prove2.me/theorems/f2645b6e-b861-4fa8-b8d7-d2ec34587ca3
-- title:
--   The law of the four runs
-- statement:
--   The joint law of $\theta$ and four data sequences that are conditionally i.i.d. given $\theta$, each with the bits of Construction C.
--
--   **Formalization Note** The prior in `θ` times counting measure on the bits, with density the product of the four `seqWeight`s. The verification file proves it is a probability measure for `0 < Δ ≤ 1/4`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 4.1, p.15

import Mathlib
import Definitions.Def_ReplicableOL_Omega4
import Definitions.Def_ReplicableOL_epochPrior
import Definitions.Def_ReplicableOL_seqWeight
open MeasureTheory ProbabilityTheory

namespace ReplicableOL

/-- **The law of the four runs.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 4.1, p.15. "Four data sequences S, S′, S″, S‴ are conditionally i.i.d. given θ, each with the law of Construction C".

**Formalization Note.** The prior in `θ` times counting measure on the bits, with density the product of the four `seqWeight`s. The verification file proves it is a probability measure for `0 < Δ ≤ 1/4`. -/
noncomputable def fourRun (Δ : ℝ) (k L : ℕ) : Measure (Omega4 k L) :=
  ((epochPrior k Δ).prod (Measure.count : Measure (Bits k L × Bits k L × Bits k L × Bits k L))).withDensity
    fun ω => ENNReal.ofReal
      (seqWeight ω.1 ω.2.1 * seqWeight ω.1 ω.2.2.1 * seqWeight ω.1 ω.2.2.2.1 * seqWeight ω.1 ω.2.2.2.2)

end ReplicableOL


