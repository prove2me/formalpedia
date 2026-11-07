-- Prove2me | Definitions.Def_ReplicableOL_sSq
-- name    : ReplicableOL_sSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:45:55.488218+00:00
-- url     : https://prove2.me/theorems/6e2ececa-59f3-44ab-b68d-199feb776077
-- title:
--   The scale $s^2$
-- statement:
--   The scale $s^2=k\sigma_x^2=\mathbb EX^2$.
--
--   **Formalization Note** `k` is a natural number cast to `ℝ`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 3, p.10

import Mathlib
import Definitions.Def_ReplicableOL_sigmaXSq

namespace ReplicableOL

/-- **The scale $s^2$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 3, p.10. `s² := kσ_x² = EX²`.

**Formalization Note.** `k` is a natural number cast to `ℝ`. -/
noncomputable def sSq (k L : ℕ) (Δ : ℝ) : ℝ := (k : ℝ) * sigmaXSq L Δ

end ReplicableOL


