-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_WittHS
-- name    : Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_WittHS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:37.705814+00:00
-- url     : https://prove2.me/theorems/ee7d903d-3283-4f92-8a7d-0f8b13cb1294
-- title:
--   Witt HS
-- statement:
--   Definitions and structural lemmas for Witt HS, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/WittHS.lean

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_FinNormSurj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.IndefR.LocBrg
section HS
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
local notation "vv" => (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))
def newtonSq (u : L) : ℕ → L
  | 0 => 1
  | k + 1 => newtonSq u k - (newtonSq u k * newtonSq u k - u) / (2 * newtonSq u k)
variable (u : L)
end HS
section HS2
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
local notation "vv" => (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))
variable (u : L)
end HS2
end Formalism.IndefR.LocBrg


