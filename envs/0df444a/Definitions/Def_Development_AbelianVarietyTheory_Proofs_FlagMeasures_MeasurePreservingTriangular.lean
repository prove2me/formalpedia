-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingTriangular
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingTriangular
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:41.616835+00:00
-- url     : https://prove2.me/theorems/acc99506-a645-46a4-a112-77d18595f29f
-- title:
--   Measure Preserving Triangular
-- statement:
--   Definitions and structural lemmas for Measure Preserving Triangular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingTriangular.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CokernelPairSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder
namespace GlobalTheory.SgLoc.TriShift
section General
variable {G : Type} [AddGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  (μ : Measure G) [SigmaFinite μ] [μ.IsAddRightInvariant]
  {ι : Type} [Fintype ι]
end General
end GlobalTheory.SgLoc.TriShift


