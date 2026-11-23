-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLintegralEqOfMeasurable
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLintegralEqOfMeasurable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:01.944566+00:00
-- url     : https://prove2.me/theorems/a6f89edf-f059-48ce-91cd-8f9c8224a87a
-- title:
--   Exists Lintegral Eq Of Measurable
-- statement:
--   Definitions and structural lemmas for Exists Lintegral Eq Of Measurable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsLintegralEqOfMeasurable.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMapMulRightEqSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
namespace GlobalTheory.IwasawaShape
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
end GlobalTheory.IwasawaShape


