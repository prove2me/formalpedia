-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEqMulApplyZero
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEqMulApplyZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:55.241815+00:00
-- url     : https://prove2.me/theorems/b751560f-dc92-493c-b8f3-b1816e9a0f81
-- title:
--   Exists Eq Mul Apply Zero
-- statement:
--   Definitions and structural lemmas for Exists Eq Mul Apply Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEqMulApplyZero.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM
noncomputable section
open scoped Classical Topology
namespace GlobalTheory.CharForm
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
def cosetInd (U : AddSubgroup X) (q : X ⧸ U) : X → ℂ := fun x => if (x : X ⧸ U) = q then 1 else 0
end GlobalTheory.CharForm


