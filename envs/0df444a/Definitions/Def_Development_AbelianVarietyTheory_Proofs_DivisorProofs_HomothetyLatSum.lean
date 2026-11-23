-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomothetyLatSum
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomothetyLatSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:01:43.871238+00:00
-- url     : https://prove2.me/theorems/3d606bce-2205-45c2-b6a7-e73cb0febd0d
-- title:
--   Homothety Lat Sum
-- statement:
--   Definitions and structural lemmas for Homothety Lat Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomothetyLatSum.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdNormSq
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
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
namespace GlobalTheory.HomothetyLatSum
variable {E : Type} [Field E] [NumberField E]
def mulQ (α : E) : Quotient (unitRel (E := E)) → Quotient (unitRel (E := E)) :=
  Quotient.map (fun x => α * x) (by rintro x x' ⟨u, h⟩; exact ⟨u, by rw [h]; ring⟩)
theorem mulQ_mk (α x : E) : mulQ α (Quotient.mk _ x) = Quotient.mk (unitRel (E := E)) (α * x) := rfl
theorem mulQ_mulQ (a b : E) (q : Quotient (unitRel (E := E))) : mulQ a (mulQ b q) = mulQ (a * b) q := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rw [mulQ_mk, mulQ_mk, mulQ_mk, mul_assoc]
theorem mulQ_one (q : Quotient (unitRel (E := E))) : mulQ 1 q = q := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rw [mulQ_mk, one_mul]
theorem mulQ_mem {α : E} (hα : α ≠ 0) {L : Set E} {q : Quotient (unitRel (E := E))} (hq : q ∈ modUnits L) :
    mulQ α q ∈ modUnits ((fun x => α * x) '' L) := by
  obtain ⟨x, hx, h0, rfl⟩ := hq
  exact ⟨α * x, ⟨x, hx, rfl⟩, mul_ne_zero hα h0, rfl⟩
theorem mulQ_inv_mem {α : E} (hα : α ≠ 0) {L : Set E} {q : Quotient (unitRel (E := E))}
    (hq : q ∈ modUnits ((fun x => α * x) '' L)) : mulQ α⁻¹ q ∈ modUnits L := by
  obtain ⟨_, ⟨x, hx, rfl⟩, h0, rfl⟩ := hq
  refine ⟨x, hx, fun h => h0 (by simp [h]), ?_⟩
  rw [mulQ_mk, inv_mul_cancel_left₀ hα]
def mulEquiv {α : E} (hα : α ≠ 0) (L : Set E) : modUnits L ≃ modUnits ((fun x => α * x) '' L) where
  toFun q := ⟨mulQ α q.1, mulQ_mem hα q.2⟩
  invFun q := ⟨mulQ α⁻¹ q.1, mulQ_inv_mem hα q.2⟩
  left_inv q := Subtype.ext (by simp only; rw [mulQ_mulQ, inv_mul_cancel₀ hα, mulQ_one])
  right_inv q := Subtype.ext (by simp only; rw [mulQ_mulQ, mul_inv_cancel₀ hα, mulQ_one])
variable {I : Type} [Fintype I]
end GlobalTheory.HomothetyLatSum


