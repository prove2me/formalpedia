-- Prove2me | Definitions.Def_TwoWayCVQKD_oneWayEve
-- name    : TwoWayCVQKD_oneWayEve
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:45:53.528987+00:00
-- url     : https://prove2.me/theorems/65ebbb1f-7c8f-4b39-8421-74193be0aac5
-- title:
--   Eve's modes $E',E''$ in the one-way model
-- statement:
--   Eve holds two modes: the output $E'$ of the beam splitter and the arm $E''$ of her EPR pair that never entered the channel. Her quantum variables are, in this order,
--   $$
--   \hat Y_E:=(\hat Q_{E'},\hat P_{E'},\hat Q_{E''},\hat P_{E''}).
--   $$
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eq. (36), p.8

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08
import Definitions.Def_TwoWayCVQKD_oneWayCloner
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eq. (36), p.8: Eve's quantum
variables `Ŷ_E := (Q̂_E', P̂_E', Q̂_E'', P̂_E'')`, with mode `E'` from the cloner and mode `E''` the
arm of the EPR pair she keeps. -/
noncomputable def oneWayEve (T : ℝ) : QuadratureIndex 2 → OneWaySrc → ℝ :=
  fun i => ![(oneWayCloner T i.2).2, Pi.single (Sum.inr (Sum.inr (Sum.inl (1, i.2)))) 1] i.1

end TwoWayCVQKD


