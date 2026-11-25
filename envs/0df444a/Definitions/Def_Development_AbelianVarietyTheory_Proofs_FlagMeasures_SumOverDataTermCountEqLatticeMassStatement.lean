-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumOverDataTermCountEqLatticeMassStatement
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumOverDataTermCountEqLatticeMassStatement
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T07:01:57.569832+00:00
-- url     : https://prove2.me/theorems/5aa82be0-c7dc-4b2d-af3c-d020eb9301f7
-- title:
--   Sum Over Data Term Count Eq Lattice Mass Statement
-- statement:
--   Definitions and structural lemmas for Sum Over Data Term Count Eq Lattice Mass Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SumOverDataTermCountEqLatticeMassStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumOverDataTermCountEqLatticeMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical


