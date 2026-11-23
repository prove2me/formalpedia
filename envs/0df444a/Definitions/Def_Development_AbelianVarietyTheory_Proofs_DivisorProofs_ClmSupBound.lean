-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:56.257969+00:00
-- url     : https://prove2.me/theorems/04a935fa-c69a-47f3-9662-3f233994e627
-- title:
--   Clm Sup Bound
-- statement:
--   Definitions and structural lemmas for Clm Sup Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClmSupBound.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SliceSchwartz
open scoped ContDiff
noncomputable section
namespace GlobalTheory.SliceOp
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
def padL {κ κ' : Type} (h : κ → V) : κ ⊕ κ' → V := Sum.elim h 0
def qOp {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (s : κ ⊕ κ₁' → V) : ℂ :=
  P (sliceR f (s ∘ Sum.inl)) (s ∘ Sum.inr)
abbrev pd {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (w : X) :
    SchwartzMap X ℂ →L[ℂ] SchwartzMap X ℂ :=
  LineDeriv.lineDerivOpCLM ℂ (SchwartzMap X ℂ) w
end GlobalTheory.SliceOp


