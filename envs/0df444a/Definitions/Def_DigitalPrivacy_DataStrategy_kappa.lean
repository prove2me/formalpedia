-- Prove2me | Definitions.Def_DigitalPrivacy_DataStrategy_kappa
-- name    : DigitalPrivacy_DataStrategy_kappa
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:05:13.475559+00:00
-- url     : https://prove2.me/theorems/48214931-4efd-46f7-b6fe-6e7fb23b8482
-- title:
--   $\kappa(C)$ of Lemma 2
-- statement:
--   For $P+(1-P)\rho>0$ define
--
--   $$\kappa(C)=\frac{1-P-P\rho C(1-\beta)}{P+(1-P)\rho} .$$
--
--   It enters the closed form of the optimal data collection for fixed protection (Lemma 2).
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), Lemma 2, p. 29 (PDF 30)

import Mathlib

namespace DigitalPrivacy.DataStrategy

/-- **`κ(C) = (1 − P − PρC(1 − β))/(P + (1 − P)ρ)`, Lemma 2.**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), Lemma 2, p. 29 (PDF 30): "Here κ(C) = (1−P−PρC(1−β))/(P+(1−P)ρ)".

**Formalization Note.** Meant for `P + (1 − P)ρ > 0` (i.e. not `P = ρ = 0`); the theorems that
use it assume this. -/
noncomputable def kappa (β ρ P C : ℝ) : ℝ :=
  (1 - P - P * ρ * C * (1 - β)) / (P + (1 - P) * ρ)

end DigitalPrivacy.DataStrategy


