-- Prove2me | Definitions.Def_PrivLittlestone_etaP
-- name    : PrivLittlestone_etaP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:31:23.568306+00:00
-- url     : https://prove2.me/theorems/322c6a52-1854-488f-9c6e-60d78f2c4f41
-- title:
--   Loss scale $\eta = \varepsilon_s/4$
-- statement:
--   The loss scale $\eta = \varepsilon_s / 4$ of (5).
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), (5), p.8

import Mathlib
import Definitions.Def_PrivLittlestone_epsS

namespace PrivLittlestone

/-- The loss scale `η = ε_s/4` (He–He, *Private Online Learning of Littlestone Classes and Matroid
Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), (5), p.8). -/
noncomputable def etaP (K m : ℕ) (ε δ : ℝ) : ℝ := epsS K m ε δ / 4

end PrivLittlestone


