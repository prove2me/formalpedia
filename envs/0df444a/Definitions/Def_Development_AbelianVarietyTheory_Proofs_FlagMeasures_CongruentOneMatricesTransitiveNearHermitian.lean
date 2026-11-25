-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitian
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitian
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T05:19:13.589007+00:00
-- url     : https://prove2.me/theorems/431ed73e-2782-5413-a905-ab758e3bb11e
-- title:
--   Congruent One Matrices Transitive Near Hermitian
-- statement:
--   Definitions and structural lemmas for Congruent One Matrices Transitive Near Hermitian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CongruentOneMatricesTransitiveNearHermitian.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
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
namespace GlobalTheory.CongTrans
open GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
section Mat
variable (L : LocE F E) {m : ℕ}
end Mat
variable [IsNonarchimedeanLocalField F]
variable [CharZero F] (L : LocE F E)
end GlobalTheory.CongTrans


