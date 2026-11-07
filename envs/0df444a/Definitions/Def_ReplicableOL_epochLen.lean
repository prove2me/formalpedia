-- Prove2me | Definitions.Def_ReplicableOL_epochLen
-- name    : ReplicableOL_epochLen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:18.487686+00:00
-- url     : https://prove2.me/theorems/e989234c-4505-47b3-a01c-3199ac8585a5
-- title:
--   The epoch length $L=\lceil c_2\sqrt T/(\rho\Delta)\rceil$
-- statement:
--   The epoch length of the main theorem,
--   $$
--   L=\left\lceil \frac{c_2\sqrt T}{\rho\Delta}\right\rceil,\qquad c_2=9\cdot10^{-10}.
--   $$
--
--   **Formalization Note** The printed constant is written as the exact rational `9 / 10^10`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Theorem 1 (precise form), p.9

import Mathlib

namespace ReplicableOL

/-- **The epoch length $L=\lceil c_2\sqrt T/(\rho\Delta)\rceil$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Theorem 1 (precise form), p.9. `c_2 := 9 · 10^{−10}` and `L := ⌈c_2 √T/(ρΔ)⌉`.

**Formalization Note.** The printed constant is written as the exact rational `9 / 10^10`. -/
noncomputable def epochLen (ρ Δ : ℝ) (T : ℕ) : ℕ :=
  ⌈(9 / 10 ^ 10 : ℝ) * √(T : ℝ) / (ρ * Δ)⌉₊

end ReplicableOL


