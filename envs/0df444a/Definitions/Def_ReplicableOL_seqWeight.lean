-- Prove2me | Definitions.Def_ReplicableOL_seqWeight
-- name    : ReplicableOL_seqWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:16.949016+00:00
-- url     : https://prove2.me/theorems/44928f85-5e23-4b17-ac68-13c71356e6fb
-- title:
--   Probability of the bits given $\theta$
-- statement:
--   The probability of the block sequence $S$ given $\theta$: $\prod_{j\le k}\nu_{\mu_j}(S_j)$.
--
--   **Formalization Note** `seqWeight θ S = ∏_j ν_{μ_j}(S_j)`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.1, p.7

import Mathlib
import Definitions.Def_ReplicableOL_Bits
import Definitions.Def_ReplicableOL_blockWeight

namespace ReplicableOL

/-- **Probability of the bits given $\theta$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.1, p.7. Given `θ`, the bits are independent with `B_t ∼ Bern(1/2 + μ_j)` for `t ∈ E_j`.

**Formalization Note.** `seqWeight θ S = ∏_j ν_{μ_j}(S_j)`. -/
noncomputable def seqWeight {k L : ℕ} (θ : Fin k → ℝ) (S : Bits k L) : ℝ :=
  ∏ j, blockWeight (θ j) (S j)

end ReplicableOL


