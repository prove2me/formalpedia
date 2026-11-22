-- Prove2me | solution 1 for Auto.HeatData.Jbar_zero_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:33:55.705722+00:00
-- url     : https://prove2.me/submissions/c429e7f2-59fb-4d07-afc7-c389eca2c695

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_energyReg_bounds
public import Theorems.Thm_Auto_sum_gweight_le
public import Theorems.Thm_Auto_HeatData_W_cube_le
public import Theorems.Thm_Auto_HeatData_energy_le_W
public import Theorems.Thm_Auto_HeatData_plane_integral_weights

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
theorem _root_.solution (hh : 0 < Hd.h) (kk : ι → ℤ) (hk : Function.Injective kk)
    (hu : ∀ i, Hd.u i = Hd.h * kk i) (α : Fin 3 → ℝ) (hα : ∀ k, 1 ≤ α k) {s : ℝ}
    (hs : Hd.h ^ 2 ≤ s) :
    Hd.Jbar α 0 s ≤ 2 * √2 * (1 + √(2 / π)) * ∑ v, Hd.nCube v := by
  set M := 1 + √(2 / π)
  set β : ℝ := 1 / 10
  have hβ : 0 < β := by norm_num
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have hα0 : ∀ k, 0 < α k := fun k => zero_lt_one.trans_le (hα k)
  set σ := HeatData.sig α s
  have hσh : ∀ k, Hd.h ^ 2 ≤ σ k := fun k => by
    simp only [σ, HeatData.sig]; nlinarith [hα k]
  have hsum : ∀ (p : Fin 3 → ℝ) k, ∑ i, Hd.w p σ k i ≤ M := fun p k =>
    sum_gweight_le Hd.u hh (hσh k) kk hk hu (p k)
  have hM : 0 ≤ M := by positivity
  set c : Fin 3 → ι → ι → ℝ := fun v i j => 2 * √2 * M * ‖Hd.A v i j‖ ^ 3
  set B : (Fin 3 → ℝ) → ℝ := fun p => ∑ v, ∑ i, ∑ j,
    c v i j * (Gm β 0 s p * (Hd.w p σ v i * Hd.w p σ (v + 1) j))
  have hpw := fun v i j => Hd.plane_integral_weights α hα0 hβ hs0 v i j
  have hBint : Integrable B := integrable_finsetSum _ fun v _ =>
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hpw v i j).1.const_mul _
  have hBval : ∫ p, B p = 2 * √2 * M * ∑ v, Hd.nCube v := by
    simp only [B]
    rw [integral_finsetSum _ fun v _ => integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => (hpw v i j).1.const_mul _]
    simp_rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hpw _ i j).1.const_mul _]
    simp_rw [integral_finsetSum _ fun j _ => (hpw _ _ j).1.const_mul _]
    simp_rw [integral_const_mul, (hpw _ _ _).2]
    simp only [c, nCube, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  have hG0 : ∀ p, 0 ≤ Gm β 0 s p := fun p => by
    simp only [Gm, gaussianD_zero]; exact gaussian_nonneg' _ _
  have hpt : ∀ p, Gm β 0 s p * ∑ v, Hd.qE α 0 v s p ≤ B p := by
    intro p
    have hW : ∀ v, hsSq (Hd.W p σ v) ^ (3 / 2 : ℝ) ≤
        M * ∑ i, ∑ j, ‖Hd.A v i j‖ ^ 3 * Hd.w p σ v i * Hd.w p σ (v + 1) j := fun v =>
      Hd.W_cube_le hh.le p σ v hM (hsum p v) (hsum p (v + 1))
    have hE : ∀ v, Hd.qE α 0 v s p ≤
        √2 * (hsSq (Hd.W p σ v) ^ (3 / 2 : ℝ) + hsSq (Hd.W p σ (v - 1)) ^ (3 / 2 : ℝ)) :=
      fun v => Hd.energy_le_W p σ v
    have e02 : (0 : Fin 3) - 1 = 2 := rfl
    have e12 : (1 : Fin 3) - 1 = 0 := rfl
    have e22 : (2 : Fin 3) - 1 = 1 := rfl
    have hsumE : ∑ v, Hd.qE α 0 v s p ≤
        2 * √2 * ∑ v, hsSq (Hd.W p σ v) ^ (3 / 2 : ℝ) := by
      have := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => hE v
      rw [Fin.sum_univ_three, Fin.sum_univ_three, e02, e12, e22] at this
      simp only [Fin.sum_univ_three]
      linarith
    have hsumW : 2 * √2 * ∑ v, hsSq (Hd.W p σ v) ^ (3 / 2 : ℝ) ≤
        ∑ v, ∑ i, ∑ j, c v i j * (Hd.w p σ v i * Hd.w p σ (v + 1) j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun v _ => ?_
      calc 2 * √2 * hsSq (Hd.W p σ v) ^ (3 / 2 : ℝ)
          ≤ 2 * √2 * (M * ∑ i, ∑ j, ‖Hd.A v i j‖ ^ 3 * Hd.w p σ v i * Hd.w p σ (v + 1) j) := by
            gcongr; exact hW v
        _ = _ := by
            simp only [c, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have : B p = Gm β 0 s p * ∑ v, ∑ i, ∑ j, c v i j * (Hd.w p σ v i * Hd.w p σ (v + 1) j) := by
      simp only [B, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (hsumE.trans hsumW) (hG0 p)
  have hnn : ∀ p, 0 ≤ Gm β 0 s p * ∑ v, Hd.qE α 0 v s p := fun p =>
    mul_nonneg (hG0 p) (Finset.sum_nonneg fun v _ =>
      (energyReg_bounds (Matrix.posSemidef_conjTranspose_mul_self _) le_rfl).1)
  calc Hd.Jbar α 0 s = ∫ p, Gm β 0 s p * ∑ v, Hd.qE α 0 v s p := rfl
    _ ≤ ∫ p, B p := integral_mono_of_nonneg (Eventually.of_forall hnn) hBint (Eventually.of_forall
        hpt)
    _ = _ := hBval
end Auto.HeatData
