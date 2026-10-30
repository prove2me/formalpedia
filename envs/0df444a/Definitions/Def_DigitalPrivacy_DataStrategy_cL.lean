-- Prove2me | Definitions.Def_DigitalPrivacy_DataStrategy_cL
-- name    : DigitalPrivacy_DataStrategy_cL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:05:28.149615+00:00
-- url     : https://prove2.me/theorems/b8b56129-991d-4f70-8803-3502eb179f7f
-- title:
--   Threshold $C_l$ of Lemma 2
-- statement:
--   Define
--
--   $$C_l=\frac1{1-\beta}\cdot\frac{2+\rho-P(1+\rho)}{P+\rho+P\rho} .$$
--
--   Lemma 2: below $C_l$ the business collects part of the data, above it all data.
--
--   **Formalization Note** Meant for $P+\rho+P\rho>0$.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), Lemma 2, p. 29 (PDF 30)

import Mathlib

namespace DigitalPrivacy.DataStrategy

/-- **The threshold `C_l = (1/(1 − β))·(2 + ρ − P(1 + ρ))/(P + ρ + Pρ)`, Lemma 2.**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), Lemma 2, p. 29 (PDF 30): "Cl = 1/(1−β) · (2+ρ−P(1+ρ))/(P+ρ+Pρ)".

**Formalization Note.** Meant for `P + ρ + Pρ > 0`, which holds whenever `P + (1 − P)ρ > 0` and
`P, ρ ∈ [0, 1]`. -/
noncomputable def cL (β ρ P : ℝ) : ℝ :=
  (1 / (1 - β)) * ((2 + ρ - P * (1 + ρ)) / (P + ρ + P * ρ))

end DigitalPrivacy.DataStrategy


