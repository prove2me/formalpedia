-- Prove2me | solution 1 for Auto.gridGaussianForm_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:40:40.937031+00:00
-- url     : https://prove2.me/submissions/ffc97469-20b1-4b7d-967e-e9338d40b4aa

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_integral_baseTrace
public import Theorems.Thm_Auto_Kern_eq
public import Theorems.Thm_Auto_continuousOn_kernIntegrand

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
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Auto
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Hd : HeatData ι) (hh : 0 < Hd.h) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    gridGaussianForm Hd a b =
      ∫ s in Set.Ioc a b, ((1 / s : ℝ) : ℂ) *
        ∫ q : Fin 2 → ℝ, Hd.baseTrace 3 (planePt q) s := by
  let F : ι → ι → ι → ℝ → ℂ := fun i j k s =>
    (Hd.h ^ 3 : ℂ) * (Hd.A 0 i j * Hd.A 1 j k * Hd.A 2 k i) *
      (kernIntegrand 3 s (Hd.u i + Hd.u j + Hd.u k) : ℂ)
  have hint : ∀ i j k, IntegrableOn (F i j k) (Set.Ioc a b) := by
    intro i j k
    apply Integrable.const_mul
    exact (((continuousOn_kernIntegrand 3 _).mono
      (fun s hs => ha.trans_le hs.1)).integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self).ofReal
  have hpt : ∀ s ∈ Set.Ioc a b,
      ((1 / s : ℝ) : ℂ) * (∫ q : Fin 2 → ℝ, Hd.baseTrace 3 (planePt q) s) =
        ∑ i, ∑ j, ∑ k, F i j k s := by
    intro s hs
    rw [(Hd.integral_baseTrace hh.le (Or.inl rfl) (ha.trans hs.1)).2]
    simp only [F, Finset.mul_sum, kernIntegrand]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hpt]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => hint i j k]
  simp_rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint _ j k]
  simp_rw [integral_finsetSum _ fun k _ => hint _ _ k]
  simp only [gridGaussianForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  simp only [F, integral_const_mul]
  rw [integral_complex_ofReal, ← intervalIntegral.integral_of_le hab, ← Kern_eq]
  ring
end Auto
