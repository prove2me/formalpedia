-- Prove2me | Definitions.Def_ReplicableOL_Tzero
-- name    : ReplicableOL_Tzero
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:16.360319+00:00
-- url     : https://prove2.me/theorems/e131a315-ce59-4432-b7e4-b0f3d18c277d
-- title:
--   The horizon threshold $T_0(\rho,\Delta)$
-- statement:
--   The threshold on the horizon in the main theorem,
--   $$
--   T_0(\rho,\Delta)=\max\{1.3\cdot10^{26}\rho^2\Delta^{-2},\ 1.3\cdot10^{22}(\rho\Delta)^2,\ 10^{-3}(\rho\Delta)^{-2}\}.
--   $$
--   Its three terms guarantee, respectively, $\Delta\sqrt L\ge100$, $L\ge100$ and $k\ge100$ together with the bound on the second term of $B_\delta$.
--
--   **Formalization Note** The printed decimals are written as exact rationals. The divisions are by positive numbers in the theorem's range `ρ, Δ > 0`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Theorem 1 (precise form), p.9

import Mathlib

namespace ReplicableOL

/-- **The horizon threshold $T_0(\rho,\Delta)$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Theorem 1 (precise form), p.9. `T_0(ρ, Δ) := max{1.3·10^{26} ρ² Δ^{−2}, 1.3·10^{22} (ρΔ)², 10^{−3} (ρΔ)^{−2}}`.

**Formalization Note.** The printed decimals are written as exact rationals. The divisions are by positive numbers in the theorem's range `ρ, Δ > 0`. -/
noncomputable def Tzero (ρ Δ : ℝ) : ℝ :=
  max (max (13 * 10 ^ 25 * ρ ^ 2 / Δ ^ 2) (13 * 10 ^ 21 * (ρ * Δ) ^ 2)) (1 / 10 ^ 3 / (ρ * Δ) ^ 2)

end ReplicableOL


