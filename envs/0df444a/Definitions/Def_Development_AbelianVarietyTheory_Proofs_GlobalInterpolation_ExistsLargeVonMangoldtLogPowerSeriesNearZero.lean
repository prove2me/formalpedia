-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLargeVonMangoldtLogPowerSeriesNearZero
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLargeVonMangoldtLogPowerSeriesNearZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:31.594433+00:00
-- url     : https://prove2.me/theorems/cc5c6a90-142c-4474-bbab-b45c84db7e4e
-- title:
--   Exists Large Von Mangoldt Log Power Series Near Zero
-- statement:
--   Definitions and structural lemmas for Exists Large Von Mangoldt Log Power Series Near Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLargeVonMangoldtLogPowerSeriesNearZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBoundRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZerosStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TuranSecondMainTheoremPowerSumsUnitCoefficientsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
namespace GlobalTheory.NearZeroDeriv
end GlobalTheory.NearZeroDeriv


