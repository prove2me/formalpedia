-- Prove2me | Definitions.Def_PrivLittlestone_LT
-- name    : PrivLittlestone_LT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:07.652953+00:00
-- url     : https://prove2.me/theorems/6abd3540-1418-4e53-bd48-3d18a800289f
-- title:
--   $L_T = \log(4K(T+1)/\beta)$
-- statement:
--   The parameter $L_T = \log\dfrac{4K(T+1)}{\beta}$ of (7).
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), (7), p.8

import Mathlib

namespace PrivLittlestone

/-- `L_T = log(4K(T + 1)/β)` (He–He, *Private Online Learning of Littlestone Classes and Matroid
Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), (7), p.8). -/
noncomputable def LT (K T : ℕ) (β : ℝ) : ℝ :=
  Real.log (4 * (K : ℝ) * ((T : ℝ) + 1) / β)

end PrivLittlestone


