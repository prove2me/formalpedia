-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermitianFormsSameSignatureSameSpace
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermitianFormsSameSignatureSameSpace
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:01:58.950674+00:00
-- url     : https://prove2.me/theorems/bfc5a16d-38f0-4f8f-a8cf-bae9927b977b
-- title:
--   Hermitian Forms Same Signature Same Space
-- statement:
--   Definitions and structural lemmas for Hermitian Forms Same Signature Same Space, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HermitianFormsSameSignatureSameSpace.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetMulVolMulConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsBinaryEqAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ConjEqNegOfSqEqNegNat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.OneSpace
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory.OneSpace
namespace GlobalTheory
open GlobalTheory.OneSpace
end GlobalTheory


