-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LeMulNormFlatOfSelfDual
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LeMulNormFlatOfSelfDual
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T15:57:03.089499+00:00
-- url     : https://prove2.me/theorems/8c7b323f-64df-4062-b61e-0778920b3121
-- title:
--   Le Mul Norm Flat Of Self Dual
-- statement:
--   Definitions and structural lemmas for Le Mul Norm Flat Of Self Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LeMulNormFlatOfSelfDual.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Theorems.Thm_GlobalTheory_TensorLat_mem_tensorLat_stdLat
import Theorems.Thm_GlobalTheory_TensorLat_norm_sq_flat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply


set_option autoImplicit false
namespace GlobalTheory.TensorLat
open NumberField ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
example (X : PT E) (x : Vsp X.dim) (hx : x ∈ X.L) (k : Fin n) :
    Pi.single k x ∈ tensorLat X (ReciprocityTheory.GeometryOfNumbersTheory.stdLat E n) ∧
      ‖flat (Pi.single k x : Fin n → Vsp X.dim)‖ ^ 2 = ‖x‖ ^ 2 := by
  constructor
  · refine mem_tensorLat_stdLat.2 fun j => ?_
    by_cases h : j = k
    · subst h; simpa using hx
    · simp [h]
  · rw [norm_sq_flat, Finset.sum_eq_single k]
    · simp
    · intro j _ h; simp [h]
    · simp
end GlobalTheory.TensorLat


