-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisHankelDetNeZeroOfLift
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisHankelDetNeZeroOfLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:24.592876+00:00
-- url     : https://prove2.me/theorems/2ab26ef4-1829-45fa-bffd-bbc69ac2a8ee
-- title:
--   Jacquet Rallis Hankel Det Ne Zero Of Lift
-- statement:
--   Definitions and structural lemmas for Jacquet Rallis Hankel Det Ne Zero Of Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisHankelDetNeZeroOfLift.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.JR.DeltaLift
variable {k : Type} [Field k] {r : ℕ}
end GlobalTheory.JR.DeltaLift


