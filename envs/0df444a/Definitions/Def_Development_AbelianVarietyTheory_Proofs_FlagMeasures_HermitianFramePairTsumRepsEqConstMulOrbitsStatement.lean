-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairTsumRepsEqConstMulOrbitsStatement
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairTsumRepsEqConstMulOrbitsStatement
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T07:43:05.274185+00:00
-- url     : https://prove2.me/theorems/a1179c71-af49-47d7-ab9d-6796c2fa0fde
-- title:
--   Hermitian Frame Pair Tsum Reps Eq Const Mul Orbits Statement
-- statement:
--   Definitions and structural lemmas for Hermitian Frame Pair Tsum Reps Eq Const Mul Orbits Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramePairTsumRepsEqConstMulOrbitsStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairTsumRepsEqConstMulOrbits
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical


