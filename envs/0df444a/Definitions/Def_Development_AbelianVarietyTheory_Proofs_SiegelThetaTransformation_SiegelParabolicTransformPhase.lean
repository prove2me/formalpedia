-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelParabolicTransformPhase
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelParabolicTransformPhase
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:52.042643+00:00
-- url     : https://prove2.me/theorems/cc0b91ad-360a-4e70-8b05-54c19806ad8d
-- title:
--   Siegel Parabolic Transform Phase
-- statement:
--   Definitions and structural lemmas for Siegel Parabolic Transform Phase, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelParabolicTransformPhase.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EqOfSiegelThetaSeriesRationalEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationSiegelParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
namespace GlobalTheory.Phase.ParabValues
open GlobalTheory.SW.Parab
end GlobalTheory.Phase.ParabValues


