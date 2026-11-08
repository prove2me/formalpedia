-- Prove2me | Definitions.Def_SpencerEight_betaRow
-- name    : SpencerEight_betaRow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:38.568745+00:00
-- url     : https://prove2.me/theorems/0348d3b6-8065-471b-85b0-7e4070df8cae
-- title:
--   Row rank coefficients $\beta_j$ of Definition 8.39
-- statement:
--   $(\beta_0,\beta_1,\beta_2)=(8.033111630413584\cdot10^{-6},\ 1.305387270607384\cdot10^{-6},\ 1.671417693169337\cdot10^{-7})$ and $\beta_j=0$ for $3\le j\le6$.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Definition 8.39, p.102 (PDF p.102)

import Mathlib

namespace SpencerEight

/-- The rank coefficients of the centered rows (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Definition 8.39, p.102 (PDF p.102)): `(β₀, β₁, β₂)` as printed and `β_j := 0` for `3 ≤ j ≤ 6`. Exact rationals. -/
noncomputable def betaRow : Fin 7 → ℝ :=
  ![8.033111630413584e-6, 1.305387270607384e-6, 1.671417693169337e-7, 0, 0, 0, 0]

end SpencerEight


