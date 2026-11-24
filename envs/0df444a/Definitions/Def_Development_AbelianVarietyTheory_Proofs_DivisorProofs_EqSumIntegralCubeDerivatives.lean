-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqSumIntegralCubeDerivatives
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqSumIntegralCubeDerivatives
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:51.494776+00:00
-- url     : https://prove2.me/theorems/0291c094-b87f-4f0e-a839-38a36448c145
-- title:
--   Eq Sum Integral Cube Derivatives
-- statement:
--   Definitions and structural lemmas for Eq Sum Integral Cube Derivatives, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqSumIntegralCubeDerivatives.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SobolevIteratedOneParameterSubgroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
namespace GlobalTheory.CubeTaylor
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
end GlobalTheory.CubeTaylor


