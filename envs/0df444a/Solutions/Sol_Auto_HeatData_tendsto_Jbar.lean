-- Prove2me | solution 1 for Auto.HeatData.tendsto_Jbar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:37:33.024022+00:00
-- url     : https://prove2.me/submissions/bd849231-cabe-4528-b97d-a2ec3c06d8ba

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_phi_nonneg
public import Theorems.Thm_Auto_HeatData_entry_bounds
public import Theorems.Thm_Auto_re_trace_le_of_entry_le
public import Theorems.Thm_Auto_energyReg_bounds
public import Theorems.Thm_Auto_HeatData_phi_le_two
public import Theorems.Thm_Auto_continuous_re_trace
public import Theorems.Thm_Auto_HeatData_continuous_mats
public import Theorems.Thm_Auto_phi_sq_mul_exp_le
public import Theorems.Thm_Auto_abs_Gm_le
public import Theorems.Thm_Auto_integrable_of_le_gdom
public import Theorems.Thm_P2M_Auto_continuous_gaussian__66693ed17080
public import Theorems.Thm_Auto_HeatData_Gm_eq
public import Theorems.Thm_Auto_HeatData_Jbar_integrable
public import Theorems.Thm_Auto_tendsto_energyReg

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι)
namespace Auto.HeatData
theorem _root_.solution (hh : 0 < Hd.h) {α : Fin 3 → ℝ} (hα1 : ∀ k, 1 ≤ α k) (hα2 : ∀ k, α k ≤ 2)
    {s : ℝ} (hs : 0 < s) {η : ℕ → ℝ} (hη0 : ∀ m, 0 < η m) (hη1 : ∀ m, η m ≤ 1)
    (hlim : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun m => Hd.Jbar α (η m) s) atTop (𝓝 (Hd.Jbar α 0 s)) := by
  set σ := sig α s
  have hσ : ∀ k, 0 < σ k := fun k => mul_pos (zero_lt_one.trans_le (hα1 k)) hs
  have hσr : ∀ k, σ k ∈ Set.Icc s (2 * s) := fun k => by
    constructor
    · simp only [σ, sig]; nlinarith [hα1 k]
    · simp only [σ, sig]; nlinarith [hα2 k]
  set L : Fin 3 → (Fin 3 → ℝ) → ℝ := fun v p => (Hd.T p σ v).trace.re
  set bnd : (Fin 3 → ℝ) → ℝ := fun p =>
    Gm (1 / 10) 0 s p * ∑ v, 2 * L v p * √(L v p + 1)
  have hTp : ∀ p v, (Hd.T p σ v).PosSemidef := fun p v =>
    Matrix.posSemidef_conjTranspose_mul_self _
  have hL0 : ∀ v p, 0 ≤ L v p := fun v p => re_trace_nonneg_of_posSemidef (hTp p v)
  have hG0 : ∀ p, 0 ≤ Gm (1 / 10) 0 s p := fun p => by rw [Gm_eq]; exact gaussian_nonneg' _ _
  have hbnd : Integrable bnd := by
    obtain ⟨C₀, hC₀, hent⟩ := Hd.entry_bounds hh.le (σa := s) (σb := 2 * s) hs (by linarith)
    obtain ⟨Cg, hCg, hG⟩ := abs_Gm_le 0 (β := 1 / 10) (by norm_num) hs (sb := s)
    set N : ℝ := (Fintype.card (ι ⊕ ι) : ℝ)
    set K := 2 * N * C₀ * √(N * (4 * C₀) + 1)
    have hK : 0 ≤ K := by positivity
    set ε := min (1 / (8 * (2 * s))) (1 / (4 * (1 / 10 * s))) / 4
    have hε : 0 < ε := by positivity
    have hc : Continuous bnd := by
      have cG : Continuous fun p : Fin 3 → ℝ => Gm (1 / 10) 0 s p := by
        have : (fun p : Fin 3 → ℝ => Gm (1 / 10) 0 s p) =
            fun p => gaussian (1 / 10 * s) (p 0 + p 1 + p 2) := by funext p; rw [Gm_eq]
        rw [this]; exact (continuous_gaussian' _).comp (by fun_prop)
      have cL : ∀ v, Continuous (L v) := fun v =>
        continuous_re_trace (Hd.continuous_mats continuous_id continuous_const
          (fun _ => hσ) v).1
      exact cG.mul (continuous_finsetSum _ fun v _ => (continuous_const.mul (cL v)).mul
        (Real.continuous_sqrt.comp ((cL v).add continuous_const)))
    refine integrable_of_le_gdom hc hε (C := Cg * K * 4 * 3) fun p => ?_
    have hφ : ∀ v, L v p ≤ N * (C₀ * phi (2 * s) v p ^ 2) := fun v =>
      re_trace_le_of_entry_le _ fun a b => ((hent p σ hσr v).1 a b).1
    have hφ2 : ∀ v, phi (2 * s) v p ≤ 2 := fun v => phi_le_two (by positivity) v p
    have hterm : ∀ v, 2 * L v p * √(L v p + 1) ≤ K * phi (2 * s) v p ^ 2 := by
      intro v
      have h1 := hφ v
      have hφ0 := phi_nonneg (2 * s) v p
      have h4 : phi (2 * s) v p ^ 2 ≤ 4 := by nlinarith [hφ2 v]
      have hL4 : L v p ≤ N * (4 * C₀) := by
        have : N * (C₀ * phi (2 * s) v p ^ 2) ≤ N * (C₀ * 4) := by gcongr
        linarith
      have hs1 : √(L v p + 1) ≤ √(N * (4 * C₀) + 1) := Real.sqrt_le_sqrt (by linarith)
      calc 2 * L v p * √(L v p + 1) ≤ 2 * (N * (C₀ * phi (2 * s) v p ^ 2)) *
            √(N * (4 * C₀) + 1) := by
            gcongr
        _ = K * phi (2 * s) v p ^ 2 := by simp only [K]; ring
    have hG1 := hG s ⟨le_rfl, le_rfl⟩ p
    rw [abs_of_nonneg (hG0 p)] at hG1
    have hdec : ∀ v, phi (2 * s) v p ^ 2 *
        Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * (1 / 10 * s))) ≤ 4 * gdom ε p := fun v =>
      phi_sq_mul_exp_le (by positivity) (by positivity) v p
    have hsumv : ∑ v, 2 * L v p * √(L v p + 1) ≤ K * ∑ v, phi (2 * s) v p ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum fun v _ => hterm v
    have hE := Real.exp_pos (-(p 0 + p 1 + p 2) ^ 2 / (4 * (1 / 10 * s)))
    have hnn : 0 ≤ ∑ v, 2 * L v p * √(L v p + 1) := Finset.sum_nonneg fun v _ =>
      mul_nonneg (mul_nonneg zero_le_two (hL0 v p)) (Real.sqrt_nonneg _)
    rw [abs_of_nonneg (mul_nonneg (hG0 p) hnn)]
    calc Gm (1 / 10) 0 s p * ∑ v, 2 * L v p * √(L v p + 1)
        ≤ (Cg * Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * (1 / 10 * s)))) *
            (K * ∑ v, phi (2 * s) v p ^ 2) := mul_le_mul hG1 hsumv hnn (by positivity)
      _ = Cg * K * ∑ v, phi (2 * s) v p ^ 2 *
            Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * (1 / 10 * s))) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun v _ => by ring
      _ ≤ Cg * K * ∑ _v : Fin 3, 4 * gdom ε p :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => hdec v) (by positivity)
      _ = Cg * K * 4 * 3 * gdom ε p := by simp; ring
  refine tendsto_integral_of_dominated_convergence bnd
    (fun m => (Hd.Jbar_integrable hh (hη0 m) hα1 hα2 hs).aestronglyMeasurable) hbnd
    (fun m => Eventually.of_forall fun p => ?_) (Eventually.of_forall fun p => ?_)
  · have hnn : 0 ≤ Gm (1 / 10) 0 s p * ∑ v, Hd.qE α (η m) v s p :=
      mul_nonneg (hG0 p) (Finset.sum_nonneg fun v _ =>
        (energyReg_bounds (hTp p v) (hη0 m).le).1)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => ?_) (hG0 p)
    have := (energyReg_bounds (hTp p v) (hη0 m).le).2
    refine this.trans ?_
    gcongr
    · exact mul_nonneg zero_le_two (hL0 v p)
    · exact hη1 m
  · refine Tendsto.const_mul _ (tendsto_finsetSum _ fun v _ => ?_)
    exact tendsto_energyReg (hTp p v).1 hlim
end Auto.HeatData
