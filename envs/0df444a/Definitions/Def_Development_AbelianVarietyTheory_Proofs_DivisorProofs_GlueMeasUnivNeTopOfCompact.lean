-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlueMeasUnivNeTopOfCompact
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlueMeasUnivNeTopOfCompact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:15.657434+00:00
-- url     : https://prove2.me/theorems/6982d82c-bce6-48f8-94fc-46872d31ddcb
-- title:
--   Glue Meas Univ Ne Top Of Compact
-- statement:
--   Definitions and structural lemmas for Glue Meas Univ Ne Top Of Compact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlueMeasUnivNeTopOfCompact.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal
namespace GlobalTheory
end GlobalTheory


