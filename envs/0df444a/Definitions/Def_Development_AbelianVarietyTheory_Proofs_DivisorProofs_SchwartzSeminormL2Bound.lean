-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormL2Bound
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormL2Bound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:50:18.980833+00:00
-- url     : https://prove2.me/theorems/5b97d47a-1ccb-4471-ba29-e32e7ca3a9a9
-- title:
--   Schwartz Seminorm L2 Bound
-- statement:
--   Definitions and structural lemmas for Schwartz Seminorm L2 Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormL2Bound.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLintegralSobolevPointwiseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralNormPowMulLeSqrtWeightedSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivIteratedFDerivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIteratedFDerivTendstoZeroCocompactStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableSqPowMulIteratedFDerivSchwartzStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzWeightedSobolevOfFinrankZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
namespace GlobalTheory
end GlobalTheory


