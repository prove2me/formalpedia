-- Prove2me | solution 1 for Auto.HeatData.gram_scalar_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:29:33.867797+00:00
-- url     : https://prove2.me/submissions/ca2cb0a7-2ea7-4dda-81fd-acf2280e1acd

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_add_smul_one_sub_posSemidef
public import Theorems.Thm_Auto_hsSq_le_of_entry_le
public import Theorems.Thm_Auto_sqrt_hsSq_le_of_entry_le
public import Theorems.Thm_Auto_re_trace_le_of_entry_le
public import Theorems.Thm_Auto_HeatData_abs_tr32_le
public import Theorems.Thm_Auto_matCost_toReal_le_hsSq
public import Theorems.Thm_Auto_energyReg_bounds

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι)
namespace Auto.HeatData
theorem _root_.solution {κ : Type*} [Fintype κ] [DecidableEq κ] {N C₀ φ η : ℝ}
    (hN : (Fintype.card κ : ℝ) ≤ N) (hC₀ : 0 ≤ C₀) (hφ : 0 ≤ φ) (hφ2 : φ ≤ 2) (hη : 0 < η)
    {Γ : Matrix κ κ ℂ} (hΓ : Γ.PosSemidef) (hΓb : ∀ a b, ‖Γ a b‖ ≤ C₀ * φ ^ 2) :
    (∀ K : Matrix κ κ ℂ, (∀ a b, ‖K a b‖ ≤ C₀ * φ ^ 2) → |tr32 η Γ K| ≤ (3 / 2) * √(N * (4 * C₀)
      + N * η) * N * C₀ * φ ^ 2 ∧ |(matCost (Γ + (η : ℂ) • 1) K).toReal| ≤ (3 / 4) * N ^ 2 * (4 *
      C₀) * C₀ / √η * φ ^ 2) ∧ |energyReg η Γ| ≤ 2 * N * C₀ * √(N * (4 * C₀) + η) * φ ^ 2 := by
  have hN0 : 0 ≤ N := (Nat.cast_nonneg _).trans hN
  have hQ : C₀ * φ ^ 2 ≤ 4 * C₀ := by nlinarith [mul_le_mul hφ2 hφ2 hφ (by norm_num : (0:ℝ) ≤ 2)]
  have hQ0 : 0 ≤ C₀ * φ ^ 2 := by positivity
  have htr : Γ.trace.re ≤ N * (C₀ * φ ^ 2) := (re_trace_le_of_entry_le Γ hΓb).trans
      (mul_le_mul_of_nonneg_right hN hQ0)
  have htr4 : Γ.trace.re ≤ N * (4 * C₀) := htr.trans (mul_le_mul_of_nonneg_left hQ hN0)
  have htr0 : 0 ≤ Γ.trace.re := re_trace_nonneg_of_posSemidef hΓ
  refine ⟨fun K hK => ⟨?_, ?_⟩, ?_⟩
  · refine (abs_tr32_le hΓ hη.le K).trans ?_
    have hs : √(hsSq K) ≤ N * (C₀ * φ ^ 2) := (sqrt_hsSq_le_of_entry_le K hQ0 hK).trans
        (mul_le_mul_of_nonneg_right hN hQ0)
    have hr : √(Γ.trace.re + Fintype.card κ * η) ≤ √(N * (4 * C₀) + N * η) :=
      Real.sqrt_le_sqrt (add_le_add htr4 (mul_le_mul_of_nonneg_right hN hη.le))
    calc 3 / 2 * √(Γ.trace.re + Fintype.card κ * η) * √(hsSq K)
        ≤ 3 / 2 * √(N * (4 * C₀) + N * η) * (N * (C₀ * φ ^ 2)) := by gcongr
      _ = _ := by ring
  · have hcost := matCost_toReal_le_hsSq hη (add_smul_one_sub_posSemidef hΓ η) K
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    refine hcost.trans ?_
    have hs := hsSq_le_of_entry_le K hK
    have hs' : hsSq K ≤ N ^ 2 * ((4 * C₀) * (C₀ * φ ^ 2)) := by
      refine hs.trans ?_
      have : (C₀ * φ ^ 2) ^ 2 ≤ (4 * C₀) * (C₀ * φ ^ 2) := by
        rw [sq]; exact mul_le_mul_of_nonneg_right hQ hQ0
      have hN2 : (Fintype.card κ : ℝ) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2
      exact mul_le_mul hN2 this (sq_nonneg _) (sq_nonneg _)
    have hsη : 0 < √η := Real.sqrt_pos.2 hη
    calc 3 / 4 * hsSq K / √η ≤ 3 / 4 * (N ^ 2 * ((4 * C₀) * (C₀ * φ ^ 2))) / √η := by gcongr
      _ = _ := by ring
  · obtain ⟨h0, h1⟩ := energyReg_bounds hΓ hη.le
    rw [abs_of_nonneg h0]
    refine h1.trans ?_
    have hr : √(Γ.trace.re + η) ≤ √(N * (4 * C₀) + η) := Real.sqrt_le_sqrt (by linarith)
    calc 2 * Γ.trace.re * √(Γ.trace.re + η) ≤ 2 * (N * (C₀ * φ ^ 2)) * √(N * (4 * C₀) + η) := by
          gcongr
      _ = _ := by ring
end Auto.HeatData
