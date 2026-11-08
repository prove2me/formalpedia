-- Prove2me | Definitions.Def_SpencerEight_etaRow
-- name    : SpencerEight_etaRow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:36.772399+00:00
-- url     : https://prove2.me/theorems/2b0ee985-6d6d-43eb-883c-6fc188299436
-- title:
--   Row variances $\eta_j$ of Definition 8.39
-- statement:
--   $(\eta_j)_{j=0}^6=(0.0442852429,\ 0.0217270503,\ 0.0136732551,\ 0.0087116729,\ 0.0065347088,\ 0.0051558179,\ 0.0017485685)$, exact rationals.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Definition 8.39, p.102 (PDF p.102)

import Mathlib

namespace SpencerEight

/-- The variances `(η_j)_{j=0}^6` of the centered rows (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Definition 8.39, p.102 (PDF p.102)). Exact rationals. -/
noncomputable def etaRow : Fin 7 → ℝ :=
  ![0.0442852429, 0.0217270503, 0.0136732551, 0.0087116729, 0.0065347088, 0.0051558179,
    0.0017485685]

end SpencerEight


