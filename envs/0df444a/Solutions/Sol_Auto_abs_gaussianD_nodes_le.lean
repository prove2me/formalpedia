-- Prove2me | solution 1 for Auto.abs_gaussianD_nodes_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:22:15.059714+00:00
-- url     : https://prove2.me/submissions/c7d53e87-735c-4d92-ba41-ef6379d8133c

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_abs_gaussianD_le_unif
public import Theorems.Thm_Auto_exp_shift_le
public import Theorems.Thm_Auto_edec_sq

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
namespace Auto
theorem _root_.solution {ι : Type*} [Finite ι] (u : ι → ℝ) (j : ℕ) {σa σb : ℝ}
    (ha : 0 < σa) (hab : σa ≤ σb) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc σa σb, ∀ q i, |gaussianD j σ (u i - q)| ≤ C * edec σb q ^ 2 := by
  let := Fintype.ofFinite ι
  obtain ⟨C, hC, h⟩ := abs_gaussianD_le_unif j (σb := σb) ha
  have hb : 0 < σb := ha.trans_le hab
  refine ⟨C * ∑ i, Real.exp (u i ^ 2 / (4 * σb)), by positivity, fun σ hσ q i => ?_⟩
  rw [edec_sq]
  calc |gaussianD j σ (u i - q)| ≤ C * Real.exp (-((u i - q) ^ 2) / (4 * σb)) := h σ hσ _
    _ ≤ C * (Real.exp (u i ^ 2 / (4 * σb)) * Real.exp (-(q ^ 2) / (8 * σb))) := by
      gcongr; exact exp_shift_le _ _ hb
    _ ≤ C * ((∑ i, Real.exp (u i ^ 2 / (4 * σb))) * Real.exp (-(q ^ 2) / (8 * σb))) := by
      gcongr
      exact Finset.single_le_sum (f := fun i => Real.exp (u i ^ 2 / (4 * σb))) (fun _ _ =>
          (Real.exp_pos _).le) (Finset.mem_univ i)
    _ = _ := by ring
end Auto
