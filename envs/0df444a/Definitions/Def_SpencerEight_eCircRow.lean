-- Prove2me | Definitions.Def_SpencerEight_eCircRow
-- name    : SpencerEight_eCircRow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:38.202557+00:00
-- url     : https://prove2.me/theorems/eeca10c2-9ee9-42c4-b4de-c28e951e0931
-- title:
--   Row exponent caps $e^\circ_j$ of Definition 8.39
-- statement:
--   $(e^\circ_j)_{j=0}^6=(0.00166795657847907232,\ 0.0000144489294827552684,\ 9.22009562386846628\cdot10^{-8},\ 3.61505180575163530\cdot10^{-10},\ 1.41033178138237065\cdot10^{-12},\ 5.60018055966625035\cdot10^{-15},\ 9.61906812911829762\cdot10^{-18})$, exact rationals.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Definition 8.39, p.102 (PDF p.102)

import Mathlib

namespace SpencerEight

/-- The rank-free exponent caps `(e°_j)_{j=0}^6` of the centered rows (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Definition 8.39, p.102 (PDF p.102)). Exact rationals. -/
noncomputable def eCircRow : Fin 7 → ℝ :=
  ![0.00166795657847907232, 0.0000144489294827552684, 9.22009562386846628e-8,
    3.61505180575163530e-10, 1.41033178138237065e-12, 5.60018055966625035e-15,
    9.61906812911829762e-18]

end SpencerEight


