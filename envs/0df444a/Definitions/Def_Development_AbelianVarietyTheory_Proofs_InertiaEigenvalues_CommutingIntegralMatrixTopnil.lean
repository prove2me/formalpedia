-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixTopnil
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixTopnil
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:59.740485+00:00
-- url     : https://prove2.me/theorems/2fcf5f60-3338-45f2-8c26-9ddcd3c83066
-- title:
--   Commuting Integral Matrix Topnil
-- statement:
--   Definitions and structural lemmas for Commuting Integral Matrix Topnil, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommutingIntegralMatrixTopnil.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormDetOneAddSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ClosedBallValuationSubringToSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
namespace GlobalTheory.UnitDiscAlg
section Residue
variable (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E]
def unitBallMaxIdeal : Ideal (unitBallSubring E) := GlobalTheory.ClosedBallValuationSubring.openBallIdeal E
end Residue
end GlobalTheory.UnitDiscAlg


