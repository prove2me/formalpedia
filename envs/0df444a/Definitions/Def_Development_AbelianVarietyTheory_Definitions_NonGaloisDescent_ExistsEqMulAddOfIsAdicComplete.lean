-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T20:16:08.140496+00:00
-- url     : https://prove2.me/theorems/f94a92fa-2523-4eae-b9f2-5e059215486f
-- title:
--   Exists Eq Mul Add Of Is Adic Complete
-- statement:
--   Definitions and structural lemmas for Exists Eq Mul Add Of Is Adic Complete, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqMulAddOfIsAdicComplete.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemSpanLPowSIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ) {a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
variable {l e}
variable [CompleteSpace K]
end GlobalTheory.BK


