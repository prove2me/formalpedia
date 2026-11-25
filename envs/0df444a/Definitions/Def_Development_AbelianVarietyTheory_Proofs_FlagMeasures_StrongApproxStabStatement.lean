-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproxStabStatement
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproxStabStatement
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T09:05:07.285062+00:00
-- url     : https://prove2.me/theorems/41e5b650-bf3f-5a48-a04b-e2f1f0d41dd1
-- title:
--   Strong Approx Stab Statement
-- statement:
--   Definitions and structural lemmas for Strong Approx Stab Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StrongApproxStabStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproxStab
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical


