-- Prove2me | solution 1 for Auto.heatCost_interval_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:41:05.81311+00:00
-- url     : https://prove2.me/submissions/4e7334b5-e3d6-4ecf-888f-df3ce0e68006

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_smeared_plane_dissipation
public import Theorems.Thm_Auto_HeatData_Jbar_zero_le
public import Theorems.Thm_Auto_HeatData_Jbar_nonneg
public import Theorems.Thm_Auto_HeatData_tendsto_Jbar
public import Theorems.Thm_Auto_HeatData_costDensity_integrable
public import Theorems.Thm_Auto_HeatData_ofReal_costDensity
public import Theorems.Thm_Auto_HeatData_ofReal_integral_Vbar
public import Theorems.Thm_Auto_matCost_tendsto_regularization

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
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Auto
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Hd : HeatData ι) {kk : ι → ℤ} (hk : Function.Injective kk)
    (hu : ∀ i, Hd.u i = Hd.h * kk i) (hh : 0 < Hd.h)
    {α : Fin 3 → ℝ} (hα : ∀ v, α v = 1 ∨ α v = 11 / 10)
    (hsum : α 0 + α 1 + α 2 = 16 / 5) {a b : ℝ}
    (ha : Hd.h ^ 2 ≤ a) (hab : a ≤ b) :
    ∫⁻ z, heatCost Hd α z ∂((volume.restrict (Set.Ioc a b)).prod volume) ≤
      ENNReal.ofReal (28 * (2 * Real.sqrt 2 * (1 + Real.sqrt (2 / Real.pi))) *
        ∑ v, Hd.nCube v) := by
  let η : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hη0 : ∀ m, 0 < η m := fun m => by positivity
  have hη1 : ∀ m, η m ≤ 1 := fun m => by
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hη : Tendsto η atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hα1 : ∀ v, 1 ≤ α v := by
    intro v
    rcases hα v with h | h <;> norm_num [h]
  have hα2 : ∀ v, α v ≤ 2 := by
    intro v
    rcases hα v with h | h <;> norm_num [h]
  let μ := (volume.restrict (Set.Ioc a b)).prod (volume : Measure (Fin 3 → ℝ))
  let f : ℕ → ℝ × (Fin 3 → ℝ) → ℝ≥0∞ :=
    fun m z => ENNReal.ofReal (Hd.costDensity α (η m) z)
  have hf : ∀ m, AEMeasurable (f m) μ := fun m =>
    (Hd.costDensity_integrable hh (hη0 m) hα1 hα2 ha0
      hab).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hpt : ∀ z, Tendsto (fun m => f m z) atTop (𝓝 (heatCost Hd α z)) := by
    intro z
    simp only [f, Hd.ofReal_costDensity (hη0 _), heatCost]
    apply ENNReal.Tendsto.const_mul _ (Or.inr ENNReal.ofReal_ne_top)
    apply tendsto_finsetSum
    intro v _
    exact matCost_tendsto_regularization (Matrix.posSemidef_conjTranspose_mul_self _)
      _ (fun m => (hη0 m).le) hη
  have hbound : ∀ m, ∫⁻ z, f m z ∂μ ≤ ENNReal.ofReal (28 * Hd.Jbar α (η m) a) := by
    intro m
    have hd := Hd.smeared_plane_dissipation α (η m) hh (hη0 m) hα hsum ha0 hab
    have hj := Hd.Jbar_nonneg α (hη0 m).le b
    rw [show (∫⁻ z, f m z ∂μ) = ENNReal.ofReal
      (∫ s in a..b, ∑ v, Hd.Vbar α (η m) v s) by
        simpa only [f, μ, Hd.ofReal_costDensity (hη0 m)] using
          (Hd.ofReal_integral_Vbar hh (hη0 m) hα1 hα2 ha0 hab).symm]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hlim : Tendsto (fun m => ENNReal.ofReal (28 * Hd.Jbar α (η m) a)) atTop
      (𝓝 (ENNReal.ofReal (28 * Hd.Jbar α 0 a))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp
      ((Hd.tendsto_Jbar hh hα1 hα2 ha0 hη0 hη1 hη).const_mul 28)
  calc
    ∫⁻ z, heatCost Hd α z ∂μ = ∫⁻ z, liminf (fun m => f m z) atTop ∂μ :=
      lintegral_congr fun z => (hpt z).liminf_eq.symm
    _ ≤ liminf (fun m => ∫⁻ z, f m z ∂μ) atTop := lintegral_liminf_le' hf
    _ ≤ ENNReal.ofReal (28 * Hd.Jbar α 0 a) := by
      rw [← hlim.liminf_eq]
      exact liminf_le_liminf (Eventually.of_forall hbound)
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have hJ := Hd.Jbar_zero_le hh kk hk hu α hα1 ha
      nlinarith)
end Auto
