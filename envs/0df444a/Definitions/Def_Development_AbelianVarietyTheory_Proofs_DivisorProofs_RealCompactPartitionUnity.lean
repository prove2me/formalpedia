-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RealCompactPartitionUnity
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_RealCompactPartitionUnity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:19.561613+00:00
-- url     : https://prove2.me/theorems/5465d9d1-ec83-4d6a-add4-3807b8f1c1f9
-- title:
--   Real Compact Partition Unity
-- statement:
--   Definitions and structural lemmas for Real Compact Partition Unity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RealCompactPartitionUnity.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff
noncomputable section
namespace GlobalTheory.LatticePartition
def bump (t : ℝ) : ℝ := Real.smoothTransition (t + 1) - Real.smoothTransition t
section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
def bumpProd (e : V ≃L[ℝ] (Fin n → ℝ)) (x : V) : ℝ := ∏ i, bump (e x i)
def latPt (e : V ≃L[ℝ] (Fin n → ℝ)) (j : Fin n → ℤ) : V := e.symm (fun i => (j i : ℝ))
end
end GlobalTheory.LatticePartition


