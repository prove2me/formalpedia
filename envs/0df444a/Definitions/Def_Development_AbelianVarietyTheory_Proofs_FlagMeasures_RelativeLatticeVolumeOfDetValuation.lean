-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuation
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:26:17.423523+00:00
-- url     : https://prove2.me/theorems/19575750-0969-4ad4-8c3c-da7555099724
-- title:
--   Relative Lattice Volume Of Det Valuation
-- statement:
--   Definitions and structural lemmas for Relative Lattice Volume Of Det Valuation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RelativeLatticeVolumeOfDetValuation.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardQuotPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardQuotPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBis
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
namespace GlobalTheory.HL.LatDet
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
end GlobalTheory.HL.LatDet


