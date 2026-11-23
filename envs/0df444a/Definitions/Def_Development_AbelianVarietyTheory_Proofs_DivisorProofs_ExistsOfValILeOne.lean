-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOfValILeOne
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOfValILeOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:35.400195+00:00
-- url     : https://prove2.me/theorems/05624d1c-57cd-48b2-998d-e06673df9549
-- title:
--   Exists Of Val ILe One
-- statement:
--   Definitions and structural lemmas for Exists Of Val ILe One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOfValILeOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ValIwasawa
open Matrix
variable {V F : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]
variable (V) in

abbrev valI : Valuation F (ValuationRing.ValueGroup V F) := ValuationRing.valuation V F
end GlobalTheory.ValIwasawa


