-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLatSmulBlockLat
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLatSmulBlockLat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:18.013298+00:00
-- url     : https://prove2.me/theorems/0f8e3d23-4e91-48ad-abcd-042c0eb8562b
-- title:
--   Mem Mat Lat Smul Block Lat
-- statement:
--   Definitions and structural lemmas for Mem Mat Lat Smul Block Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemMatLatSmulBlockLat.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel
open scoped Pointwise
noncomputable section
namespace GlobalTheory.SplitFlip.FourierDepth
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type*} [DecidableEq D]
variable [Fintype A] [DecidableEq A]
end GlobalTheory.SplitFlip.FourierDepth


