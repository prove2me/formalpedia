-- Prove2me | Definitions.Def_SteinitzExchange_Duality_Supplement_CharacteristicCounterexample
-- name    : SteinitzExchange_Duality_Supplement_CharacteristicCounterexample
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:28:06.111638+00:00
-- url     : https://prove2.me/theorems/d630e7b5-5c39-4d11-90c6-ebf2bb261c89
-- title:
--   Data refuting the printed converse of Theorem 5.4
-- statement:
--   On $V=\{1,2\}$ define
--   $$B=\{(2,0),(1,1),(0,2)\},\qquad (\omega(2,0),\omega(1,1),\omega(0,2))=(0,-10,0).$$
--   These are the concrete data of the supplement's counterexample to printed Theorem 5.4. They are constructed for the source audit rather than definitions asserted by the paper. `characteristicValue` is total and zero away from $(1,1)$; only its values on $B$ matter.
-- source:
--   Moderator counterexample to Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 293, Theorem 5.4

import Mathlib

namespace SteinitzExchange.Duality.Supplement

/-- The hole-free integral segment used to refute printed Theorem 5.4. -/
def characteristicBase : Finset (Fin 2 → ℤ) :=
  {![2, 0], ![1, 1], ![0, 2]}

/-- Values (0,-10,0) on the three points of characteristicBase. -/
noncomputable def characteristicValue (x : Fin 2 → ℤ) : ℝ :=
  if x = ![1, 1] then -10 else 0

end SteinitzExchange.Duality.Supplement


