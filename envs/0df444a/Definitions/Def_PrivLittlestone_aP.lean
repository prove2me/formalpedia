-- Prove2me | Definitions.Def_PrivLittlestone_aP
-- name    : PrivLittlestone_aP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:33:42.08771+00:00
-- url     : https://prove2.me/theorems/0802f164-979d-4cab-b8bc-81a5f2592c9d
-- title:
--   Rank scale $a = \eta + \log(8B/\tau)$
-- statement:
--   The rank scale $a = \eta + \log(8B/\tau)$ of (6), with $\eta$ from (5) and $\tau$ from (6).
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), (6), p.8

import Mathlib
import Definitions.Def_PrivLittlestone_etaP
import Definitions.Def_PrivLittlestone_tauP

namespace PrivLittlestone

/-- The rank scale `a = η + log(8B/τ)` (He–He, *Private Online Learning of Littlestone Classes and
Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), (6), p.8), with `η` from
(5) and `τ` from (6). -/
noncomputable def aP (K m T : ℕ) (B ε δ : ℝ) : ℝ :=
  etaP K m ε δ + Real.log (8 * B / tauP K m T δ)

end PrivLittlestone


