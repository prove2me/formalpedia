-- Prove2me | Definitions.Def_ReplicableOL_gain
-- name    : ReplicableOL_gain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:49:17.753377+00:00
-- url     : https://prove2.me/theorems/4a40c227-bf60-4303-9e6d-4f6372e0d0f9
-- title:
--   Data-dependent gain $\Gamma$
-- statement:
--   The **data-dependent gain** $\Gamma=\sum_j2L\mu_j(\bar p_j-p_j)$: what a learner gains by reacting to the data of the current epoch. Replicability limits it through Theorem 2.
--
--   **Formalization Note** A function of `(θ, S)` at a fixed seed, with `p_j = frac Φ j (hist S j) (S j)`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.2, p.8

import Mathlib
import Definitions.Def_ReplicableOL_pbar
import Definitions.Def_ReplicableOL_hist

namespace ReplicableOL

/-- **Data-dependent gain $\Gamma$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.2, p.8. `Γ := Σ_j 2Lμ_j(p̄_j − p_j)`.

**Formalization Note.** A function of `(θ, S)` at a fixed seed, with `p_j = frac Φ j (hist S j) (S j)`. -/
noncomputable def gain {k L : ℕ} (Δ : ℝ) (Φ : EpochRule k L) (θ : Fin k → ℝ) (S : Bits k L) : ℝ :=
  ∑ j : Fin k, 2 * (L : ℝ) * θ j * (pbar Δ Φ j (hist S j) - frac Φ j (hist S j) (S j))

end ReplicableOL


