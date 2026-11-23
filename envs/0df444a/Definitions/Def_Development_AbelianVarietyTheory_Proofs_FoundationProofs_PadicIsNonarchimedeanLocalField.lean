-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:43.741789+00:00
-- url     : https://prove2.me/theorems/1797a60d-bd93-41ba-a475-5519630fd5fb
-- title:
--   Padic Is Nonarchimedean Local Field
-- statement:
--   Definitions and structural lemmas for Padic Is Nonarchimedean Local Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise Topology
noncomputable section
namespace GlobalTheory.SplitWeil
section Padic
variable (p : ℕ) [Fact p.Prime]
theorem padic_valuation_lt_iff (x y : ℚ_[p]) :
    valuation ℚ_[p] x < valuation ℚ_[p] y ↔ ‖x‖ < ‖y‖ := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [(isEquiv (valuation ℚ_[p]) Padic.mulValuation).lt_iff_lt]
  by_cases hy : y = 0
  · simp [hy]
  by_cases hx : x = 0
  · simp [hx, hy, zero_lt_iff]
  rw [Padic.norm_eq_zpow_log_mulValuation hx, Padic.norm_eq_zpow_log_mulValuation hy,
    zpow_lt_zpow_iff_right₀ hp, WithZero.log_lt_log (by simpa using hx) (by simpa using hy)]
instance padic_isValuativeTopology : IsValuativeTopology ℚ_[p] := by
  refine IsValuativeTopology.of_zero fun s => ?_
  rw [Metric.mem_nhds_iff]
  constructor
  · rintro ⟨ε, hε, hs⟩
    obtain ⟨y, hy0, hy⟩ := NormedField.exists_norm_lt ℚ_[p] hε
    refine ⟨Units.mk0 (valuation ℚ_[p] y) (by simpa using norm_pos_iff.mp hy0), fun z hz => hs ?_⟩
    rw [mem_ball_zero_iff]
    exact ((padic_valuation_lt_iff p z y).mp hz).trans hy
  · rintro ⟨γ, hs⟩
    obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero ℚ_[p])
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact γ.ne_zero (by simpa using hy.symm)
    refine ⟨‖y‖, norm_pos_iff.mpr hy0, fun z hz => hs ?_⟩
    rw [mem_ball_zero_iff] at hz
    show valuation ℚ_[p] z < γ
    rw [← hy]
    exact (padic_valuation_lt_iff p z y).mpr hz
instance padic_isNonarchimedeanLocalField : IsNonarchimedeanLocalField ℚ_[p] where
end Padic
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
def cball (s : kˣ) : Set k := {x | valuation k x ≤ valuation k (s : k)}
section Meas
variable [MeasurableSpace k] [BorelSpace k]
end Meas
section Om
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
def sideMul (g : GL a k) (h : GL b k) : Matrix b a k ≃ₜ Matrix b a k where
  toFun x := (h⁻¹ : GL b k).val * x * g.val
  invFun x := h.val * x * (g⁻¹ : GL a k).val
  left_inv x := by
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  right_inv x := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
end Om
section Char
def ratCircle : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp⟩)
variable {ψ : AddChar k Circle} {c : kˣ}
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
end Char
end GlobalTheory.SplitWeil


