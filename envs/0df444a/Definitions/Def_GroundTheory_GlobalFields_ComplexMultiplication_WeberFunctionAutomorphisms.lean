-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunctionAutomorphisms
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_WeberFunctionAutomorphisms
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:45.056486+00:00
-- url     : https://prove2.me/theorems/2a42847c-8090-40ee-bcf1-6833d6c2f9e8
-- title:
--   Weber Function Automorphisms
-- statement:
--   Definitions and structural lemmas for Weber Function Automorphisms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunctionAutomorphisms.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
import Theorems.Thm_GroundTheory_Global_variableChangePoint_zero
import Theorems.Thm_GroundTheory_Global_variableChange_rst_eq_zero
import Theorems.Thm_GroundTheory_Global_weberFunction_some
import Theorems.Thm_GroundTheory_Global_weberFunction_zero
import Theorems.Thm_P2M_GroundTheory_Global_IsShortForm_a__ne_zero_or_a__ne_zero_4cc4d6e7c199
import Theorems.Thm_P2M_GroundTheory_Global_variableChange_a__of_isShortForm_87451d3b79c6
import Theorems.Thm_P2M_GroundTheory_Global_variableChange_a__of_isShortForm_97ca09bc4117
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.variableChangePoint_zero
attribute [local simp] GroundTheory.Global.weberFunction_some
attribute [local simp] GroundTheory.Global.weberFunction_zero


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Global
open WeierstrassCurve OnePoint ShortWeierstrass
variable {F : Type*} [Field F]
open scoped Classical in

noncomputable def automorphismOrder (W : WeierstrassCurve F) : ℕ :=
  if W.a₆ = 0 then 4 else if W.a₄ = 0 then 6 else 2
def automorphismScale (W : WeierstrassCurve F) :
    MulAction.stabilizer (VariableChange F) W →* Fˣ where
  toFun ξ := ξ.1.u
  map_one' := rfl
  map_mul' _ _ := rfl
def automorphismPoint {W : WeierstrassCurve F} (ξ : MulAction.stabilizer (VariableChange F) W) :
    W.toAffine.Point → W.toAffine.Point :=
  variableChangePoint ξ.1 (MulAction.mem_stabilizer_iff.mp ξ.2)
section CharZero
variable [CharZero F] {W : WeierstrassCurve F}
theorem automorphism_rst_eq_zero (hW : IsShortForm W)
    (ξ : MulAction.stabilizer (VariableChange F) W) : ξ.1.r = 0 ∧ ξ.1.s = 0 ∧ ξ.1.t = 0 :=
  variableChange_rst_eq_zero hW ((MulAction.mem_stabilizer_iff.mp ξ.2).symm ▸ hW)
theorem automorphismScale_injective (hW : IsShortForm W) :
    Function.Injective (automorphismScale W) := by
  intro ξ η h
  obtain ⟨hr, hs, ht⟩ := automorphism_rst_eq_zero hW ξ
  obtain ⟨hr', hs', ht'⟩ := automorphism_rst_eq_zero hW η
  apply Subtype.ext
  exact VariableChange.ext h (hr.trans hr'.symm) (hs.trans hs'.symm) (ht.trans ht'.symm)
theorem mem_range_automorphismScale (hW : IsShortForm W) (u : Fˣ) :
    u ∈ (automorphismScale W).range ↔
      (↑u⁻¹ : F) ^ 4 * W.a₄ = W.a₄ ∧ (↑u⁻¹ : F) ^ 6 * W.a₆ = W.a₆ := by
  constructor
  · rintro ⟨ξ, rfl⟩
    have hξ : ξ.1 • W = W := MulAction.mem_stabilizer_iff.mp ξ.2
    have hCW : IsShortForm (ξ.1 • W) := hξ.symm ▸ hW
    have h4 := variableChange_a₄_of_isShortForm hW hCW
    have h6 := variableChange_a₆_of_isShortForm hW hCW
    rw [hξ] at h4 h6
    exact ⟨h4.symm, h6.symm⟩
  · rintro ⟨h4, h6⟩
    have hC : (⟨u, 0, 0, 0⟩ : VariableChange F) • W = W := by
      ext
      · simp [variableChange_a₁, hW.a₁_eq]
      · simp [variableChange_a₂, hW.a₂_eq, hW.a₁_eq]
      · simp [variableChange_a₃, hW.a₃_eq, hW.a₁_eq]
      · simpa [variableChange_a₄, hW.a₁_eq, hW.a₂_eq, hW.a₃_eq] using h4
      · simpa [variableChange_a₆, hW.a₁_eq, hW.a₂_eq, hW.a₃_eq] using h6
    exact ⟨⟨_, MulAction.mem_stabilizer_iff.mpr hC⟩, rfl⟩
variable [W.IsElliptic]
omit [CharZero F] in

theorem scale_conditions_iff (hW : IsShortForm W) (w : F) :
    (w⁻¹ ^ 4 * W.a₄ = W.a₄ ∧ w⁻¹ ^ 6 * W.a₆ = W.a₆) ↔ w ^ automorphismOrder W = 1 := by
  have key : ∀ (k : ℕ) (c : F), c ≠ 0 → (w⁻¹ ^ k * c = c ↔ w ^ k = 1) := by
    intro k c hc
    rw [inv_pow]
    constructor
    · intro h
      exact inv_eq_one.mp (mul_right_cancel₀ hc (h.trans (one_mul c).symm))
    · intro h
      rw [h, inv_one, one_mul]
  unfold automorphismOrder
  by_cases h6 : W.a₆ = 0
  · have h4 : W.a₄ ≠ 0 := by
      rcases hW.a₄_ne_zero_or_a₆_ne_zero with h | h
      · exact h
      · exact absurd h6 h
    simp only [h6, mul_zero, and_true, if_true]
    exact key 4 _ h4
  by_cases h4 : W.a₄ = 0
  · simp only [h4, h6, mul_zero, true_and, if_false, if_true]
    exact key 6 _ h6
  · simp only [h4, h6, if_false, key 4 _ h4, key 6 _ h6]
    constructor
    · rintro ⟨a, b⟩
      have : w ^ 6 = w ^ 4 * w ^ 2 := by ring
      rw [this, a, one_mul] at b
      exact b
    · intro h
      refine ⟨?_, ?_⟩
      · rw [show w ^ 4 = (w ^ 2) ^ 2 by ring, h, one_pow]
      · rw [show w ^ 6 = (w ^ 2) ^ 3 by ring, h, one_pow]
theorem range_automorphismScale (hW : IsShortForm W) :
    (automorphismScale W).range = rootsOfUnity (automorphismOrder W) F := by
  ext u
  rw [mem_range_automorphismScale hW, mem_rootsOfUnity', Units.val_inv_eq_inv_val]
  exact scale_conditions_iff hW _
noncomputable def automorphismEquivRootsOfUnity (hW : IsShortForm W) :
    MulAction.stabilizer (VariableChange F) W ≃* rootsOfUnity (automorphismOrder W) F :=
  (MonoidHom.ofInjective (automorphismScale_injective hW)).trans
    (MulEquiv.subgroupCongr (range_automorphismScale hW))
end CharZero
section Fibres
variable [CharZero F] {W : WeierstrassCurve F} [W.IsElliptic]
end Fibres
end GroundTheory.Global


