-- Prove2me | Definitions.Def_ProtonElectronMassRatio_constants
-- name    : ProtonElectronMassRatio_constants
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T19:51:33.08678+00:00
-- url     : https://prove2.me/theorems/9e8285f6-ce7b-4bfe-b851-52230e151936
-- title:
--   Constants for the Lenz coincidence: $6\pi^5$, CODATA 2022 and the 1951 datum
-- statement:
--   The five real constants the mission is stated in terms of.
--
--   - `lenzExpression` is $L = 6\pi^5$, the closed-form expression Lenz compared with the mass ratio in 1951.
--   - `codataValue` is $\mu_{2022} = 1836.152673426$, the CODATA 2022 recommended value of $m_p/m_e$.
--   - `codataUncertainty` is $u_{2022} = 3.2\times10^{-8}$, the standard uncertainty attached to it (the "(32)" on the last two digits).
--   - `lenz1951Measurement` is $\mu_{1951} = 1836.12$, the experimental value available in 1951, and `lenz1951Uncertainty` is its quoted uncertainty $u_{1951} = 0.05$.
--
--   Decimal literals denote the exact rational numbers they spell, viewed in $\mathbb{R}$.
-- source:
--   Wikipedia, "Proton-to-electron mass ratio", revision 1371273020, https://en.wikipedia.org/w/index.php?title=Proton-to-electron_mass_ratio&oldid=1371273020 — lead section (CODATA 2022 value 1836.152673426(32)) and the section "A mathematical coincidence" (F. Lenz, Phys. Rev. 82 (1951) 554, value 1836.12 ± 0.05 vs 6π⁵)

import Mathlib

namespace ProtonElectronMassRatio

/-- Lenz's 1951 expression `6 * π ^ 5`. -/
noncomputable def lenzExpression : ℝ := 6 * Real.pi ^ 5

/-- The CODATA 2022 recommended value of the proton-to-electron mass ratio. -/
def codataValue : ℝ := 1836.152673426

/-- The standard uncertainty of the CODATA 2022 value. -/
def codataUncertainty : ℝ := 0.000000032

/-- The experimental value of the mass ratio available to Lenz in 1951. -/
def lenz1951Measurement : ℝ := 1836.12

/-- The uncertainty quoted with the 1951 experimental value. -/
def lenz1951Uncertainty : ℝ := 0.05

end ProtonElectronMassRatio


