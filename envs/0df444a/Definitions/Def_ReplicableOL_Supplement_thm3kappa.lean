-- Prove2me | Definitions.Def_ReplicableOL_Supplement_thm3kappa
-- name    : ReplicableOL_Supplement_thm3kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:20:28.713955+00:00
-- url     : https://prove2.me/theorems/5a94bd9a-979d-4125-b79e-71ad0a4d2a36
-- title:
--   Parameter $\kappa$ of Theorem 3
-- statement:
--   The chain parameter of Theorem 3:
--
--   $$
--   \kappa=\frac{\rho H}{2.93\,\bar K\,T}=\frac{4.62}{2.93}\cdot\frac{\sqrt\rho}{\sqrt{\bar K}\,T^{1/4}} .
--   $$
--
--   **Formalization Note** Defined by the first expression; it is used only for $\rho>0$, $\bar K\ge1$, $T\ge1$.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Theorem 3 (with parameters), p.20

import Mathlib
import Definitions.Def_ReplicableOL_Supplement_thm3H

namespace ReplicableOL.Supplement

/-- **Theorem 3's $\kappa := \rho H/(2.93\,\bar K T)$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Theorem 3 (with parameters), p.20.

**Formalization Note.** Used only under `ρ > 0`, `K̄ ≥ 1`, `T ≥ 1`, where the denominator is positive. -/
noncomputable def thm3kappa (ρ : ℝ) (T : ℕ) : ℝ :=
  ρ * thm3H ρ T / (2.93 * (Kbar T : ℝ) * T)

end ReplicableOL.Supplement


