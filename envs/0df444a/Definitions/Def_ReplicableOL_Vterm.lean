-- Prove2me | Definitions.Def_ReplicableOL_Vterm
-- name    : ReplicableOL_Vterm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:49:23.945195+00:00
-- url     : https://prove2.me/theorems/9407ab2c-0907-4b71-8345-c45affcfad69
-- title:
--   Predictable term $V$
-- statement:
--   The **predictable term** $V=\sum_j(1-2\bar p_j)L\mu_j$ of the regret identity.
--
--   **Formalization Note** A function of `(θ, S)` at a fixed seed.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.2, p.8

import Mathlib
import Definitions.Def_ReplicableOL_pbar
import Definitions.Def_ReplicableOL_hist

namespace ReplicableOL

/-- **Predictable term $V$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.2, p.8. `V := Σ_j (1 − 2p̄_j) L μ_j`.

**Formalization Note.** A function of `(θ, S)` at a fixed seed. -/
noncomputable def Vterm {k L : ℕ} (Δ : ℝ) (Φ : EpochRule k L) (θ : Fin k → ℝ) (S : Bits k L) : ℝ :=
  ∑ j : Fin k, (1 - 2 * pbar Δ Φ j (hist S j)) * (L : ℝ) * θ j

end ReplicableOL


