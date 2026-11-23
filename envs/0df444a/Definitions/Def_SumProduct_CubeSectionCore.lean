-- Prove2me | Definitions.Def_SumProduct_CubeSectionCore
-- name    : SumProduct_CubeSectionCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T23:55:33.329015+00:00
-- url     : https://prove2.me/theorems/69f3dc1a-457e-4866-a147-7022aad8e503
-- title:
--   Cube Section Core
-- statement:
--   Definitions and structural lemmas for Cube Section Core, from Mathlib Initiative and contributors's pinned A real sum-product counterexample conditional on Martinet’s tower theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Theorems.Thm_SumProduct_mem_boxMult
import Theorems.Thm_SumProduct_mem_cubeSection
attribute [local simp] SumProduct.mem_boxMult
attribute [local simp] SumProduct.mem_cubeSection


set_option autoImplicit true
open MeasureTheory
open scoped ENNReal MeasureTheory FourierTransform
namespace SumProduct
noncomputable section
def unitCube (n : ℕ) : Set (Fin n → ℝ) :=
  Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ))
def coordSum (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i
def uniformCubeMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  (volume (unitCube n))⁻¹ • volume.restrict (unitCube n)
def uniformIntervalMeasure : Measure ℝ :=
  ((2 : NNReal)⁻¹) • volume.restrict (Set.Icc (-1 : ℝ) 1)
def cubeSumLaw (n : ℕ) : Measure ℝ :=
  (uniformCubeMeasure n).map (coordSum n)
theorem measurable_coordSum (n : ℕ) : Measurable (coordSum n) := by
  exact Finset.measurable_sum Finset.univ fun i _ => measurable_pi_apply i
theorem volume_unitCube (n : ℕ) :
    volume (unitCube n) = ENNReal.ofReal ((2 : ℝ) ^ n) := by
  rw [unitCube, Real.volume_Icc_pi]
  norm_num
instance instIsProbabilityMeasure_uniformIntervalMeasure :
    IsProbabilityMeasure uniformIntervalMeasure where
  measure_univ := by
    simp [uniformIntervalMeasure, Real.volume_Icc, ENNReal.smul_def, smul_eq_mul]
    rw [show ENNReal.ofReal (1 + 1 : ℝ) = (2 : ℝ≥0∞) by norm_num]
    exact ENNReal.inv_mul_cancel (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
theorem Measure.pi_const_smul {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (c : NNReal) (μ : (i : ι) → Measure (α i))
    [∀ i, IsFiniteMeasure (μ i)] :
    Measure.pi (fun i => c • μ i) = (c ^ Fintype.card ι) • Measure.pi μ := by
  classical
  refine Measure.pi_eq (μ := fun i => c • μ i) (μ' := (c ^ Fintype.card ι) • Measure.pi μ)
    fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul]
  simp [Measure.smul_apply, Finset.prod_mul_distrib, Finset.prod_const, ENNReal.coe_pow]
theorem uniformCubeMeasure_eq_pi_uniformIntervalMeasure (n : ℕ) :
    uniformCubeMeasure n = Measure.pi fun _ : Fin n => uniformIntervalMeasure := by
  rw [uniformCubeMeasure, volume_unitCube, unitCube, ← Set.pi_univ_Icc]
  rw [volume_pi, Measure.restrict_pi_pi]
  rw [uniformIntervalMeasure]
  rw [Measure.pi_const_smul]
  simp [ENNReal.smul_def, ENNReal.ofReal_pow, ENNReal.inv_pow, ENNReal.coe_pow,
    ENNReal.coe_inv]
instance instIsProbabilityMeasure_uniformCubeMeasure (n : ℕ) :
    IsProbabilityMeasure (uniformCubeMeasure n) := by
  rw [uniformCubeMeasure_eq_pi_uniformIntervalMeasure]
  infer_instance
instance instIsProbabilityMeasure_cubeSumLaw (n : ℕ) :
    IsProbabilityMeasure (cubeSumLaw n) := by
  rw [cubeSumLaw]
  exact Measure.isProbabilityMeasure_map (measurable_coordSum n).aemeasurable
noncomputable def cubeSumLawSuccDensity (n : ℕ) (z : ℝ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ, (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (2 : ℝ≥0∞)⁻¹) (z - x) ∂cubeSumLaw n
end
end SumProduct


