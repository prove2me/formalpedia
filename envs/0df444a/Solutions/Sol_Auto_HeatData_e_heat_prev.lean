-- Prove2me | solution 1 for Auto.HeatData.e_heat_prev
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:20:58.194693+00:00
-- url     : https://prove2.me/submissions/252a950e-5040-4141-a416-965617694a77

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_gram_heat_identity
public import Theorems.Thm_Auto_HeatData_e_eq_S
public import Theorems.Thm_Auto_HeatData_dw_def
public import Theorems.Thm_Auto_HeatData_ddw_def
public import Theorems.Thm_Auto_HeatData_fin3_ne_pred
public import Theorems.Thm_Auto_HeatData_Bprev_update
public import Theorems.Thm_Auto_HeatData_S_update_prev
public import Theorems.Thm_P2M_Auto_HeatData_S_update_prev___eeb366000557
public import Theorems.Thm_Auto_HeatData_S_psd

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
    HasDerivAt (fun q => Hd.e (Function.update p (v - 1) q) σ η v) (tr32 η (Hd.S p σ v)
      (Hd.Pprev p σ v)) (p (v - 1)) ∧ HasDerivAt (fun q => tr32 η (Hd.S (Function.update p (v - 1)
      q) σ v) (Hd.Pprev (Function.update p (v - 1) q) σ v)) (Hd.Yprev p σ η v + tr32 η (Hd.S p σ
      v) (wGram (Hd.Bprev p σ v) (Hd.ddw p σ (v - 1)))) (p (v - 1)) ∧ HasDerivAt (fun τ => Hd.e p
      (Function.update σ (v - 1) τ) η v) (tr32 η (Hd.S p σ v) (wGram (Hd.Bprev p σ v) (fun i =>
      Hd.ddw p σ (v - 1) i / 2))) (σ (v - 1)) := by
  obtain ⟨h1, h2, h3⟩ := gram_heat_identity _ (S_psd Hd p σ hh hσ v (v + 1)).2 (Hd.Bprev p σ v)
    Hd.u hh hη (hσ (v - 1)) (p (v - 1))
  have hS0 : Hd.S p σ v = wGram (Hd.Bnext p σ v) (Hd.w p σ (v + 1)) +
      wGram (Hd.Bprev p σ v) (gweight Hd.u Hd.h (σ (v - 1)) (p (v - 1))) := by
    have := S_update_prev Hd p σ hh hσ v (p (v - 1))
    rwa [Function.update_eq_self] at this
  have hP : ∀ q, Hd.Pprev (Function.update p (v - 1) q) σ v =
      wGram (Hd.Bprev p σ v) (fun i => -(Hd.h * gaussianD 1 (σ (v - 1)) (Hd.u i - q))) := by
    intro q; rw [Pprev, Bprev_update Hd p σ (fin3_ne_pred v).symm, dw_def]; simp
  refine ⟨?_, ?_, ?_⟩
  · have e1 : (fun q => Hd.e (Function.update p (v - 1) q) σ η v) = fun q => energyReg η (wGram
      (Hd.Bnext p σ v) (Hd.w p σ (v + 1)) +
          wGram (Hd.Bprev p σ v) (gweight Hd.u Hd.h (σ (v - 1)) q)) := by
      funext q; rw [e_eq_S, S_update_prev Hd p σ hh hσ]
    rw [e1, tr32, hS0, Pprev, dw_def]
    exact h1
  · have e1 : (fun q => tr32 η (Hd.S (Function.update p (v - 1) q) σ v) (Hd.Pprev (Function.update p
      (v - 1) q) σ v)) = fun q => (3 / 2) * ((CFC.sqrt (wGram (Hd.Bnext p σ v) (Hd.w p σ (v + 1)) +
            wGram (Hd.Bprev p σ v) (gweight Hd.u Hd.h (σ (v - 1)) q) + (η : ℂ) • 1) *
          wGram (Hd.Bprev p σ v) (fun i => -(Hd.h * gaussianD 1 (σ (v - 1)) (Hd.u i -
              q)))).trace).re := by
      funext q; rw [tr32, S_update_prev Hd p σ hh hσ, hP]
    rw [e1, Yprev, tr32, hS0, Pprev, dw_def, ddw_def]
    exact h2
  · have e1 : (fun τ => Hd.e p (Function.update σ (v - 1) τ) η v) =ᶠ[𝓝 (σ (v - 1))]
        fun τ => energyReg η (wGram (Hd.Bnext p σ v) (Hd.w p σ (v + 1)) +
          wGram (Hd.Bprev p σ v) (gweight Hd.u Hd.h τ (p (v - 1)))) := by
      filter_upwards [lt_mem_nhds (hσ (v - 1))] with τ hτ
      rw [e_eq_S, S_update_prev_σ Hd p σ hh hσ v hτ]
    rw [tr32, hS0, ddw_def]
    exact h3.congr_of_eventuallyEq e1
end Auto.HeatData
