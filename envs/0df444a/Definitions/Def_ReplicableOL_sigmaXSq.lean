-- Prove2me | Definitions.Def_ReplicableOL_sigmaXSq
-- name    : ReplicableOL_sigmaXSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:30.453187+00:00
-- url     : https://prove2.me/theorems/92345da5-4ccc-414c-b6ed-bca384b641db
-- title:
--   The scale $\sigma_x^2$
-- statement:
--   The variance scale of one epoch's contribution to $X$: $\sigma_x^2=\mathbb Ex_j^2=L^2\Delta^2/3+L(1/4-\Delta^2/3)$.
--
--   **Formalization Note** `L` is a natural number cast to `ℝ`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 3, p.10

import Mathlib

namespace ReplicableOL

/-- **The scale $\sigma_x^2$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 3, p.10. `σ_x² := E x_j² = L²Δ²/3 + L(1/4 − Δ²/3)`.

**Formalization Note.** `L` is a natural number cast to `ℝ`. -/
noncomputable def sigmaXSq (L : ℕ) (Δ : ℝ) : ℝ :=
  (L : ℝ) ^ 2 * Δ ^ 2 / 3 + (L : ℝ) * (1 / 4 - Δ ^ 2 / 3)

end ReplicableOL


