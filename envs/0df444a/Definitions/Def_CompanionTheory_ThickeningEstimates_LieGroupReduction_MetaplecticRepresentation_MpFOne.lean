-- Prove2me | Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MpFOne
-- name    : CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MpFOne
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T23:12:32.929936+00:00
-- url     : https://prove2.me/theorems/98ff5960-1a80-4c52-ab82-c2f67c8f3955
-- title:
--   Mp FOne
-- statement:
--   Definitions and structural lemmas for Mp FOne, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MpFOne.lean

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Theorems.Thm_CompanionTheory_ThKR_LL_mq_apply
import Theorems.Thm_CompanionTheory_ThKR_LL_vf_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff RealInnerProductSpace
namespace CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
theorem mq_add' (S T : Eu l →L[ℝ] Eu l) (g : Sch l) : mq (S + T) g = mq S g + mq T g := by
  ext x
  simp only [mq_apply, SchwartzMap.add_apply, ContinuousLinearMap.add_apply, inner_add_right]
  push_cast
  ring
theorem mq_smul' (c : ℝ) (S : Eu l →L[ℝ] Eu l) (g : Sch l) : mq (c • S) g = c • mq S g := by
  ext x
  simp only [mq_apply, SchwartzMap.smul_apply, ContinuousLinearMap.smul_apply, inner_smul_right, Complex.real_smul]
  push_cast
  ring
theorem vf_add' (H K : Eu l →L[ℝ] Eu l) (g : Sch l) : vf (H + K) g = vf H g + vf K g := by
  ext x
  simp only [vf_apply, SchwartzMap.add_apply, ContinuousLinearMap.add_apply, map_add]
theorem vf_smul' (c : ℝ) (H : Eu l →L[ℝ] Eu l) (g : Sch l) : vf (c • H) g = c • vf H g := by
  ext x
  simp only [vf_apply, SchwartzMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul]
def qdLin (f : Sch l) : Mat l →ₗ[ℝ] Sch l where
  toFun X := Qd X f
  map_add' X Y := by
    have ht : (X + Y).toBlocks₁₁ = X.toBlocks₁₁ + Y.toBlocks₁₁ := Matrix.ext fun _ _ => rfl
    simp only [Qd, map_add, neg_add, mq_add', vf_add', ht, trace_add, add_div, ofReal_add, add_smul]
    abel
  map_smul' c X := by
    have ht : (c • X).toBlocks₁₁ = c • X.toBlocks₁₁ := Matrix.ext fun _ _ => rfl
    have hc : ((c • X.toBlocks₁₁.trace / 2 : ℝ) : ℂ) • f = c • (((X.toBlocks₁₁.trace / 2 : ℝ) : ℂ) • f) := by
      rw [smul_eq_mul, mul_div_assoc, ofReal_mul, mul_smul, Complex.coe_smul]
    simp only [Qd, map_smul, ← smul_neg, mq_smul', vf_smul', ht, trace_smul, RingHom.id_apply]
    rw [hc, (fou l).map_smul_of_tower, smul_sub, smul_add, smul_add]
end CompanionTheory.ThKR.Mp


