-- Prove2me | solution 1 for Auto.HeatData.weight_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:23:59.183834+00:00
-- url     : https://prove2.me/submissions/321c8764-ac8b-40b0-b619-5e591516494a

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_P2M_Auto_gweight_nonneg__bb3decd414c3
public import Theorems.Thm_Auto_edec_pos
public import Theorems.Thm_Auto_abs_gaussianD_nodes_le

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
omit [DecidableEq ι] [Fintype ι]
namespace Auto.HeatData
theorem _root_.solution [Finite ι] (hh : 0 ≤ Hd.h) {σa σb : ℝ} (ha : 0 < σa) (hab : σa ≤ σb) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p σ : Fin 3 → ℝ, (∀ k, σ k ∈ Set.Icc σa σb) → ∀ k i, |Hd.w p σ k i| ≤ C *
      edec σb (p k) ^ 2 ∧ |Hd.dw p σ k i| ≤ C * edec σb (p k) ^ 2 ∧ |Hd.ddw p σ k i| ≤ C * edec σb
      (p k) ^ 2 ∧ Hd.sqw p σ k i ≤ √C * edec σb (p k) := by
  obtain ⟨C0, hC0, h0⟩ := abs_gaussianD_nodes_le Hd.u 0 ha hab
  obtain ⟨C1, hC1, h1⟩ := abs_gaussianD_nodes_le Hd.u 1 ha hab
  obtain ⟨C2, hC2, h2⟩ := abs_gaussianD_nodes_le Hd.u 2 ha hab
  set C := Hd.h * (C0 + C1 + C2)
  have hC : 0 ≤ C := by positivity
  have hE : ∀ x, 0 ≤ edec σb x ^ 2 := fun x => sq_nonneg _
  refine ⟨C, hC, fun p σ hσ k i => ?_⟩
  have hw : |Hd.w p σ k i| ≤ C * edec σb (p k) ^ 2 := by
    have := h0 (σ k) (hσ k) (p k) i
    rw [gaussianD_zero] at this
    simp only [w, gweight, abs_mul, abs_of_nonneg hh, C]
    calc Hd.h * |gaussian (σ k) (Hd.u i - p k)| ≤ Hd.h * (C0 * edec σb (p k) ^ 2) := by
          gcongr
      _ ≤ _ := by have := hE (p k); nlinarith [mul_nonneg hh this]
  refine ⟨hw, ?_, ?_, ?_⟩
  · have := h1 (σ k) (hσ k) (p k) i
    simp only [dw, abs_neg, abs_mul, abs_of_nonneg hh, C]
    calc Hd.h * |gaussianD 1 (σ k) (Hd.u i - p k)| ≤ Hd.h * (C1 * edec σb (p k) ^ 2) := by
          gcongr
      _ ≤ _ := by have := hE (p k); nlinarith [mul_nonneg hh this]
  · have := h2 (σ k) (hσ k) (p k) i
    simp only [ddw, abs_mul, abs_of_nonneg hh, C]
    calc Hd.h * |gaussianD 2 (σ k) (Hd.u i - p k)| ≤ Hd.h * (C2 * edec σb (p k) ^ 2) := by
          gcongr
      _ ≤ _ := by have := hE (p k); nlinarith [mul_nonneg hh this]
  · have hw0 : 0 ≤ Hd.w p σ k i := gweight_nonneg' _ hh _ _ i
    rw [sqw, ← Real.sqrt_sq (edec_pos σb (p k)).le, ← Real.sqrt_mul hC]
    exact Real.sqrt_le_sqrt ((le_abs_self _).trans hw)
end Auto.HeatData
