-- Prove2me | Definitions.Def_TwoWayCVQKD_twoWayEve
-- name    : TwoWayCVQKD_twoWayEve
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:46:50.628481+00:00
-- url     : https://prove2.me/theorems/767b1124-b87e-41a3-8c52-7f6833449b79
-- title:
--   Eve's modes $E_1',E_1'',E_2',E_2''$ in the two-way model
-- statement:
--   Eve holds four modes: the outputs $E_1',E_2'$ of her two beam splitters and the arms $E_1'',E_2''$ of her two EPR pairs. Her quantum variables are, in this order,
--   $$
--   \hat Y_E:=(\hat Q_{E_1'},\hat P_{E_1'},\hat Q_{E_1''},\hat P_{E_1''},\hat Q_{E_2'},\hat P_{E_2'},\hat Q_{E_2''},\hat P_{E_2''}).
--   $$
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eq. (74), p.9

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08
import Definitions.Def_TwoWayCVQKD_twoWayBackward
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eq. (74), p.9: Eve's quantum
variables `Ŷ_E := (Q̂_E₁', P̂_E₁', Q̂_E₁'', P̂_E₁'', Q̂_E₂', P̂_E₂', Q̂_E₂'', P̂_E₂'')`. -/
noncomputable def twoWayEve (T : ℝ) : QuadratureIndex 4 → TwoWaySrc → ℝ :=
  fun i => ![(twoWayForward T i.2).2, Pi.single (Sum.inr (Sum.inr (Sum.inl (1, i.2)))) 1,
    (twoWayBackward T i.2).2, Pi.single (Sum.inr (Sum.inr (Sum.inr (Sum.inl (1, i.2))))) 1] i.1

end TwoWayCVQKD


