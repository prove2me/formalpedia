-- Prove2me | Definitions.Def_DigitalPrivacy_DataStrategy_psiL
-- name    : DigitalPrivacy_DataStrategy_psiL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:06:24.710233+00:00
-- url     : https://prove2.me/theorems/30c53617-0673-4bbf-a14d-116982809717
-- title:
--   Lower threshold $\psi_L$
-- statement:
--   Define
--
--   $$\psi_L=\frac{(P+\rho+P\rho)^2}{4(1+\rho)} .$$
--
--   It is the protection cost at which the interior root $\xi_i$ equals $1$; for $\psi\le\psi_L$ the business collects all data.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), proof of Theorem 1 (App. A.2), p. 30 (PDF 31), unnumbered

import Mathlib

namespace DigitalPrivacy.DataStrategy

/-- **The lower threshold `ψ_L = (P + ρ + Pρ)²/(4(1 + ρ))`.**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), proof of Theorem 1 (App. A.2), p. 30 (PDF 31), unnumbered: "ψL = (P+ρ+Pρ)²/(4(1+ρ)) is a
solution to ξi = 1 wrt ψ". -/
noncomputable def psiL (ρ P : ℝ) : ℝ :=
  (P + ρ + P * ρ) ^ 2 / (4 * (1 + ρ))

end DigitalPrivacy.DataStrategy


