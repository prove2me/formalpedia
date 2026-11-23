-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TotalDegreeCMulXMulX
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TotalDegreeCMulXMulX
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:01.799315+00:00
-- url     : https://prove2.me/theorems/5d4c877d-77a9-48c6-b158-d9a423e81909
-- title:
--   Total Degree CMul XMul X
-- statement:
--   Definitions and structural lemmas for Total Degree CMul XMul X, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TotalDegreeCMulXMulX.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NormUnits
variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
def intRing : Subring K where
  carrier := Metric.closedBall 0 1
  mul_mem' {a b} ha hb := by
    simp only [mem_closedBall_zero_iff] at *
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [mem_closedBall_zero_iff] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha
theorem norm_le_one (x : intRing K) : ‖(x : K)‖ ≤ 1 := mem_closedBall_zero_iff.1 x.2
def maxIdeal : Ideal (intRing K) where
  carrier := {x | ‖(x : K)‖ < 1}
  add_mem' {a b} ha hb := by
    show ‖(a : K) + b‖ < 1
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
  zero_mem' := by show ‖((0 : intRing K) : K)‖ < 1; simp
  smul_mem' c x hx := by
    show ‖(c : K) * x‖ < 1
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one K c)).trans_lt hx
theorem mem_maxIdeal (x : intRing K) : x ∈ maxIdeal K ↔ ‖(x : K)‖ < 1 := Iff.rfl
instance maxIdeal_isMaximal : (maxIdeal K).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h => by rw [mem_maxIdeal] at h; simp at h, fun J x hle hx hxJ => ?_⟩
  rw [mem_maxIdeal, not_lt] at hx
  have h1 : ‖(x : K)‖ = 1 := le_antisymm (norm_le_one K x) hx
  have hx0 : (x : K) ≠ 0 := by intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
  let y : intRing K := ⟨(x : K)⁻¹, mem_closedBall_zero_iff.2 (by rw [norm_inv, h1, inv_one])⟩
  have hyx : y * x = 1 := Subtype.ext (by simp [y, inv_mul_cancel₀ hx0])
  rw [← hyx]; exact J.mul_mem_left y hxJ
end GlobalTheory.NormUnits
namespace GlobalTheory.NormUnits
open MvPolynomial
variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
abbrev Res : Type := intRing K ⧸ maxIdeal K
instance : Field (Res K) := Ideal.Quotient.field _
end GlobalTheory.NormUnits
namespace GlobalTheory.NormUnits
variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
end GlobalTheory.NormUnits


