-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PrincipalSeriesSubquotientOfCharacters
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_PrincipalSeriesSubquotientOfCharacters
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T21:50:43.471711+00:00
-- url     : https://prove2.me/theorems/04c74ef3-6e6d-45de-badd-d9d1f5f8ff87
-- title:
--   Principal Series Subquotient Of Characters
-- statement:
--   Definitions and structural lemmas for Principal Series Subquotient Of Characters, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PrincipalSeriesSubquotientOfCharacters.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open scoped TensorProduct
namespace GlobalTheory.PrinProd
end GlobalTheory.PrinProd


