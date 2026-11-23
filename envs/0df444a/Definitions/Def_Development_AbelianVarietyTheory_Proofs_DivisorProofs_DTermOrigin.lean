-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:13.353037+00:00
-- url     : https://prove2.me/theorems/020fa68c-d590-4d38-a774-778329e4cd99
-- title:
--   DTerm Origin
-- statement:
--   Definitions and structural lemmas for DTerm Origin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DTermOrigin.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_DefiningCoordinates
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


set_option autoImplicit false
noncomputable section
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates
namespace GlobalTheory.DeformedSum
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
def dTerm (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (z : I → ℂ) (x : E) : ℂ :=
  ∏ i, (((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), ((k : ℂ) + j)) * (starRingEnd ℂ (φ i x)) ^ m i *
    (defCoord φ z x i)⁻¹ ^ (k + m i))
example (φ : E →+* ℂ) (x : E) :
    dTerm (fun _ : Unit => φ) 4 (fun _ => 1) 0 x = -4 * (starRingEnd ℂ (φ x)) * (φ x)⁻¹ ^ 5 := by
  simp [dTerm, defCoord]
end GlobalTheory.DeformedSum


