-- Prove2me | Definitions.Def_PrivLittlestone_tauP
-- name    : PrivLittlestone_tauP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:05.485132+00:00
-- url     : https://prove2.me/theorems/c84710a1-50a7-444d-a194-76e6b4392438
-- title:
--   $\tau = \delta/(16Km(T+1))$
-- statement:
--   The parameter $\tau = \dfrac{\delta}{16 K m (T+1)}$ of (6).
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), (6), p.8

import Mathlib

namespace PrivLittlestone

/-- `τ = δ/(16 K m (T + 1))` (He–He, *Private Online Learning of Littlestone Classes and Matroid
Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), (6), p.8). -/
noncomputable def tauP (K m T : ℕ) (δ : ℝ) : ℝ :=
  δ / (16 * (K : ℝ) * (m : ℝ) * ((T : ℝ) + 1))

end PrivLittlestone


