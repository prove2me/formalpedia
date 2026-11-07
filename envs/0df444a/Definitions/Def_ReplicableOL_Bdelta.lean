-- Prove2me | Definitions.Def_ReplicableOL_Bdelta
-- name    : ReplicableOL_Bdelta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:45:23.329097+00:00
-- url     : https://prove2.me/theorems/e9876004-338e-42a7-a414-df08b66d6c84
-- title:
--   The tail bound $B_\delta(x)$
-- statement:
--   The tail bound on the gain in Theorem 2(iv),
--   $$
--   B_\delta(x)=\frac8\delta C_B\Delta^2L^{3/2}x+4L\Delta\sqrt{C_B\Delta\sqrt L\,x/\delta}.
--   $$
--
--   **Formalization Note** The square root is read at `x ≥ 0`, as in every use in the mission (`x = ρ(r)` or `x = ρ/ν`). `L` is a natural number cast to `ℝ`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Theorem 2 (formal)(iv), p.9

import Mathlib
import Definitions.Def_ReplicableOL_CB

namespace ReplicableOL

/-- **The tail bound $B_\delta(x)$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Theorem 2 (formal)(iv), p.9. `B_δ(x) := (8/δ) C_B Δ² L^{3/2} x + 4LΔ √(C_B Δ √L x/δ)`.

**Formalization Note.** The square root is read at `x ≥ 0`, as in every use in the mission (`x = ρ(r)` or `x = ρ/ν`). `L` is a natural number cast to `ℝ`. -/
noncomputable def Bdelta (Δ : ℝ) (L : ℕ) (δ x : ℝ) : ℝ :=
  8 / δ * CB * Δ ^ 2 * (L : ℝ) ^ (3 / 2 : ℝ) * x + 4 * (L : ℝ) * Δ * √(CB * Δ * √(L : ℝ) * x / δ)

end ReplicableOL


