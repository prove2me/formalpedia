-- Prove2me | Definitions.Def_ReplicableOL_Supplement_thm3H
-- name    : ReplicableOL_Supplement_thm3H
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:19:42.545477+00:00
-- url     : https://prove2.me/theorems/2af19e11-b269-44f3-a572-54282b71a972
-- title:
--   Level scale $H$ of Theorem 3
-- statement:
--   The level scale of Theorem 3:
--
--   $$
--   H=4.62\,\sqrt{\bar K}\,\frac{T^{3/4}}{\sqrt\rho}.
--   $$
--
--   **Formalization Note** $T^{3/4}$ is a real power of the cast of $T$; $4.62$ is the exact rational.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Theorem 3 (with parameters), p.20

import Mathlib
import Definitions.Def_ReplicableOL_Supplement_Kbar

namespace ReplicableOL.Supplement

/-- **Theorem 3's level scale $H := 4.62\sqrt{\bar K}\,T^{3/4}/\sqrt\rho$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Theorem 3 (with parameters), p.20.

**Formalization Note.** `T^{3/4}` is a real power of the cast. -/
noncomputable def thm3H (ρ : ℝ) (T : ℕ) : ℝ :=
  4.62 * √(Kbar T : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) / √ρ

end ReplicableOL.Supplement


