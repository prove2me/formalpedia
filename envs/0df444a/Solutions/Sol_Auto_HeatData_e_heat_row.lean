-- Prove2me | solution 1 for Auto.HeatData.e_heat_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:21:07.824141+00:00
-- url     : https://prove2.me/submissions/b8bda425-d493-4aaa-8df7-8de171cf534a

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_gram_heat_identity
public import Theorems.Thm_Auto_HeatData_dw_def
public import Theorems.Thm_Auto_HeatData_ddw_def
public import Theorems.Thm_Auto_HeatData_Brow_update
public import Theorems.Thm_Auto_HeatData_T_update
public import Theorems.Thm_P2M_Auto_HeatData_T_update___6afbb602a2e7

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
variable (Hd : HeatData ι) (p σ : Fin 3 → ℝ)
namespace Auto.HeatData
theorem _root_.solution (hh : 0 ≤ Hd.h) {η : ℝ} (hη : 0 < η) (hσ : ∀ k, 0 < σ k) (v : Fin 3) :
    HasDerivAt (fun q => Hd.e (Function.update p v q) σ η v) (tr32 η (Hd.T p σ v) (Hd.Ui p σ v))
      (p v) ∧ HasDerivAt (fun q => tr32 η (Hd.T (Function.update p v q) σ v) (Hd.Ui
      (Function.update p v q) σ v)) (Hd.V p σ η v + tr32 η (Hd.T p σ v) (wGram (Hd.Brow p σ v)
      (Hd.ddw p σ v))) (p v) ∧ HasDerivAt (fun τ => Hd.e p (Function.update σ v τ) η v) (tr32 η
      (Hd.T p σ v) (wGram (Hd.Brow p σ v) (fun i => Hd.ddw p σ v i / 2))) (σ v) := by
  obtain ⟨h1, h2, h3⟩ := gram_heat_identity 0 Matrix.PosSemidef.zero (Hd.Brow p σ v) Hd.u hh hη (hσ
      v) (p v)
  have hT0 : Hd.T p σ v = 0 + wGram (Hd.Brow p σ v) (gweight Hd.u Hd.h (σ v) (p v)) := by
    have := T_update Hd p σ hh hσ v (p v)
    rwa [Function.update_eq_self] at this
  have hUi : ∀ q, Hd.Ui (Function.update p v q) σ v =
      wGram (Hd.Brow p σ v) (fun i => -(Hd.h * gaussianD 1 (σ v) (Hd.u i - q))) := by
    intro q; rw [Ui, Brow_update, dw_def]; simp
  refine ⟨?_, ?_, ?_⟩
  · have e1 : (fun q => Hd.e (Function.update p v q) σ η v) =
        fun q => energyReg η (0 + wGram (Hd.Brow p σ v) (gweight Hd.u Hd.h (σ v) q)) := by
      funext q; rw [e, T_update Hd p σ hh hσ]
    rw [e1, tr32, hT0, Ui, dw_def]
    exact h1
  · have e1 : (fun q => tr32 η (Hd.T (Function.update p v q) σ v) (Hd.Ui (Function.update p v q) σ
      v)) = fun q => (3 / 2) * ((CFC.sqrt (0 +
          wGram (Hd.Brow p σ v) (gweight Hd.u Hd.h (σ v) q) + (η : ℂ) • 1) *
          wGram (Hd.Brow p σ v) (fun i => -(Hd.h * gaussianD 1 (σ v) (Hd.u i - q)))).trace).re := by
      funext q; rw [tr32, T_update Hd p σ hh hσ, hUi]
    rw [e1, V, tr32, hT0, Ui, dw_def, ddw_def]
    exact h2
  · have e1 : (fun τ => Hd.e p (Function.update σ v τ) η v) =ᶠ[𝓝 (σ v)]
        fun τ => energyReg η (0 + wGram (Hd.Brow p σ v) (gweight Hd.u Hd.h τ (p v))) := by
      filter_upwards [lt_mem_nhds (hσ v)] with τ hτ
      rw [e, T_update_σ Hd p σ hh hτ]
    rw [tr32, hT0, ddw_def]
    exact h3.congr_of_eventuallyEq e1
end Auto.HeatData
