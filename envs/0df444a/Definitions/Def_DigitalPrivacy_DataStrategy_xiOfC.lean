-- Prove2me | Definitions.Def_DigitalPrivacy_DataStrategy_xiOfC
-- name    : DigitalPrivacy_DataStrategy_xiOfC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:05:56.89092+00:00
-- url     : https://prove2.me/theorems/9bb91783-8c6f-4a76-9201-818ed9839cb6
-- title:
--   Interior collection $-\kappa(C)+\sqrt{{\kappa(C)^2+C(1-\beta)}}$ of Lemma 2
-- statement:
--   Define
--
--   $$\xi^\star(C)=-\kappa(C)+\sqrt{\kappa(C)^2+C(1-\beta)} .$$
--
--   By Lemma 2 this is the optimal data collection when the protection level is $C<C_l$.
--
--   **Formalization Note** Defined by the formula for every $C$; it is identified with the optimum only for $C<C_l$.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), Lemma 2, p. 29 (PDF 30)

import Mathlib
import Definitions.Def_DigitalPrivacy_DataStrategy_kappa

namespace DigitalPrivacy.DataStrategy

/-- **Lemma 2's interior collection `−κ(C) + √(κ(C)² + C(1 − β))`.**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), Lemma 2, p. 29 (PDF 30): "part of the information ξ⋆(C) = −κ(C) + √(κ(C)² + C(1 − β)) < 1
(increasing in C) if data protection policy level is low C < Cl".

**Formalization Note.** This is the closed-form expression for every `C`; Lemma 2 identifies it
with the optimal collection only for `C < C_l` (for `C > C_l` the optimum is `1`). -/
noncomputable def xiOfC (β ρ P C : ℝ) : ℝ :=
  -kappa β ρ P C + Real.sqrt (kappa β ρ P C ^ 2 + C * (1 - β))

end DigitalPrivacy.DataStrategy


