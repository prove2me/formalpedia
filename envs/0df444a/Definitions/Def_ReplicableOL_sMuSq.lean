-- Prove2me | Definitions.Def_ReplicableOL_sMuSq
-- name    : ReplicableOL_sMuSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:34.793728+00:00
-- url     : https://prove2.me/theorems/628a9d89-cf99-4c93-bff8-f151b767b0cc
-- title:
--   The scale $s_\mu^2$
-- statement:
--   The scale $s_\mu^2=kL^2\Delta^2/3$, the variance of $\sum_jL\mu_j$.
--
--   **Formalization Note** `k` and `L` are natural numbers cast to `ℝ`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 3, p.10

import Mathlib

namespace ReplicableOL

/-- **The scale $s_\mu^2$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 3, p.10. `σ_μ² := Var(Lμ_j) = L²Δ²/3` and `s_μ² := kσ_μ²`.

**Formalization Note.** `k` and `L` are natural numbers cast to `ℝ`. -/
noncomputable def sMuSq (k L : ℕ) (Δ : ℝ) : ℝ := (k : ℝ) * ((L : ℝ) ^ 2 * Δ ^ 2 / 3)

end ReplicableOL


