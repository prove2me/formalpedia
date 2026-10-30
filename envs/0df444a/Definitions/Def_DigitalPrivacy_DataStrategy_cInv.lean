-- Prove2me | Definitions.Def_DigitalPrivacy_DataStrategy_cInv
-- name    : DigitalPrivacy_DataStrategy_cInv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:06:09.337376+00:00
-- url     : https://prove2.me/theorems/43fb4d7e-9fb2-4958-bd33-fd90b4882b75
-- title:
--   $C_{{inv}}(\xi)$, inverse of Lemma 2's interior collection
-- statement:
--   Define
--
--   $$C_{inv}(\xi)=\frac1{1-\beta}\cdot\frac{\xi\,[(P+(1-P)\rho)\xi+2(1-P)]}{P+(1-P)\rho+2\xi P\rho} .$$
--
--   It solves $-\kappa(C)+\sqrt{\kappa(C)^2+C(1-\beta)}=\xi$ for $C$; optimal strategies are intersections of the curves $C=C_{inv}(\xi)$ and $C=C_h(\xi)$.
--
--   **Formalization Note** Meant for $P+(1-P)\rho>0$ and $\xi\ge0$.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), proof of Theorem 1 (App. A.2), p. 29 (PDF 30), unnumbered

import Mathlib

namespace DigitalPrivacy.DataStrategy

/-- **`C_inv(ξ) = (1/(1 − β))·ξ[(P + (1 − P)ρ)ξ + 2(1 − P)]/(P + (1 − P)ρ + 2ξPρ)`.**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), proof of Theorem 1 (App. A.2), p. 29 (PDF 30), unnumbered: "Denote Cinv(ξ) solution to
−κ(C) + √(κ(C)² + C(1 − β)) = ξ wrt C … Cinv(ξ) = 1/(1 − β) · ξ[(P + (1 − P)ρ)ξ + 2(1 − P)]/(P +
(1 − P)ρ + 2ξPρ)."

**Formalization Note.** Meant for `P + (1 − P)ρ > 0` and `ξ ≥ 0`, where the denominator is
positive. -/
noncomputable def cInv (β ρ P ξ : ℝ) : ℝ :=
  (1 / (1 - β)) * (ξ * ((P + (1 - P) * ρ) * ξ + 2 * (1 - P)) / (P + (1 - P) * ρ + 2 * ξ * P * ρ))

end DigitalPrivacy.DataStrategy


