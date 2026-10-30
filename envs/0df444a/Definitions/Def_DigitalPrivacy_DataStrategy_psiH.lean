-- Prove2me | Definitions.Def_DigitalPrivacy_DataStrategy_psiH
-- name    : DigitalPrivacy_DataStrategy_psiH
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:06:37.851424+00:00
-- url     : https://prove2.me/theorems/e4ee10f5-78d4-4fd0-87f9-cbd9eb9ccc08
-- title:
--   Upper threshold $\psi_H$
-- statement:
--   For $P<1$ define
--
--   $$\psi_H=\frac{(P+(1-P)\rho)^2}{4(1-P)} .$$
--
--   It is the protection cost at which $\xi_i=0$; for $\psi\ge\psi_H$ the business collects no data.
--
--   **Formalization Note** Meant for $P<1$ ($\psi_H=+\infty$ at $P=1$). Statements that range over $P=1$ write $\psi\ge\psi_H$ as $(P+(1-P)\rho)^2\le4(1-P)\psi$.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), proof of Theorem 1 (App. A.2), p. 30 (PDF 31), unnumbered

import Mathlib

namespace DigitalPrivacy.DataStrategy

/-- **The upper threshold `ψ_H = (P + (1 − P)ρ)²/(4(1 − P))`.**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), proof of Theorem 1 (App. A.2), p. 30 (PDF 31), unnumbered: "ψH = (P+(1−P)ρ)²/(4(1−P)) is a
solution to ξi = 0 wrt ψ".

**Formalization Note.** Meant for `P < 1` (at `P = 1` the threshold is `+∞`; Lean's `x/0 = 0`
would give `0`). Statements that range over `P = 1` write `ψ ≥ ψ_H` as
`(P + (1 − P)ρ)² ≤ 4(1 − P)ψ` instead of using this definition. -/
noncomputable def psiH (ρ P : ℝ) : ℝ :=
  (P + (1 - P) * ρ) ^ 2 / (4 * (1 - P))

end DigitalPrivacy.DataStrategy


