-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemAdjoinGlActionOfCommuteTensorPerm
-- name    : Development_AbelianVarietyTheory_Proofs_HeightProofs_MemAdjoinGlActionOfCommuteTensorPerm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:43.785186+00:00
-- url     : https://prove2.me/theorems/61e6d8ec-e546-4cec-bb11-7a51c8818cc4
-- title:
--   Mem Adjoin Gl Action Of Commute Tensor Perm
-- statement:
--   Definitions and structural lemmas for Mem Adjoin Gl Action Of Commute Tensor Perm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemAdjoinGlActionOfCommuteTensorPerm.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
namespace GlobalTheory.SymmTensor
variable {n d : ℕ}
def tens (X : Fin d → Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ :=
  Matrix.of fun I K => ∏ p, X p (I p) (K p)
def sym (X : Fin d → Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ :=
  ∑ π : Equiv.Perm (Fin d), tens (X ∘ π)
end GlobalTheory.SymmTensor
end


