-- Prove2me | Definitions.Def_ReplicableOL_xi
-- name    : ReplicableOL_xi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:49:26.751209+00:00
-- url     : https://prove2.me/theorems/afb087d1-8b94-43fb-85b8-2c64ec3e8f5a
-- title:
--   The pre-disagreement gain increment $\xi_j$
-- statement:
--   The increment $\xi_j=M_{j-1}2L\mu_j(\bar p_j-p_j)$ of the pre-disagreement part $\Gamma^{\mathrm{pre}}=\sum_j\xi_j$ of the gain.
--
--   **Formalization Note** 0-based, so `M Φ j` is the paper's `M_{j−1}`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Proposition A.17, p.35

import Mathlib
import Definitions.Def_ReplicableOL_M
import Definitions.Def_ReplicableOL_pbar
import Definitions.Def_ReplicableOL_hist

namespace ReplicableOL

/-- **The pre-disagreement gain increment $\xi_j$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Proposition A.17, p.35. `ξ_j := M_{j−1} 2Lμ_j(p̄_j − p_j)`.

**Formalization Note.** 0-based, so `M Φ j` is the paper's `M_{j−1}`. -/
noncomputable def xi {k L : ℕ} (Δ : ℝ) (Φ : EpochRule k L) (j : Fin k) (θ : Fin k → ℝ) (S S' : Bits k L) : ℝ :=
  M Φ j S S' * (2 * (L : ℝ) * θ j * (pbar Δ Φ j (hist S j) - frac Φ j (hist S j) (S j)))

end ReplicableOL


