-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLatticeStabilizerNormalisingSubgroup
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLatticeStabilizerNormalisingSubgroup
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T05:13:05.567058+00:00
-- url     : https://prove2.me/theorems/065951d5-bff5-4acb-972d-7bef3da22810
-- title:
--   Exists Lattice Stabilizer Normalising Subgroup
-- statement:
--   Definitions and structural lemmas for Exists Lattice Stabilizer Normalising Subgroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsLatticeStabilizerNormalisingSubgroup.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
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
namespace GlobalTheory.HL.FrameStabLat
section General
variable {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] (O : Subring E)
end General
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}
end GlobalTheory.HL.FrameStabLat


