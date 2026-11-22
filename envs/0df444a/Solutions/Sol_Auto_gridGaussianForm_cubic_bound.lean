-- Prove2me | solution 1 for Auto.gridGaussianForm_cubic_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:43:13.169647+00:00
-- url     : https://prove2.me/submissions/c942325d-ff33-4cf4-af36-7fb89a6cd153

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_rateAt_cases
public import Theorems.Thm_Auto_rateAt_sum
public import Theorems.Thm_Auto_constD_spec
public import Theorems.Thm_Auto_heatCost_interval_bound
public import Theorems.Thm_Auto_heatCost_aemeasurable
public import Theorems.Thm_Auto_heatTrace_bound
public import Theorems.Thm_Auto_gridGaussianForm_eq
public import Theorems.Thm_Auto_heatBoundConstant_nonneg

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
    (Hd : HeatData ι) {kk : ι → ℤ} (hk : Function.Injective kk)
    (hu : ∀ i, Hd.u i = Hd.h * kk i) (hh : 0 < Hd.h)
    {a b : ℝ} (ha : Hd.h ^ 2 ≤ a) (hab : a ≤ b) :
    ‖gridGaussianForm Hd a b‖ ≤ heatBoundConstant * ∑ v, Hd.nCube v := by
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hα1 : ∀ v k, 1 ≤ rateAt v k := by
    intro v k
    rcases rateAt_cases v k with h | h <;> norm_num [h]
  have hα2 : ∀ v k, rateAt v k ≤ 2 := by
    intro v k
    rcases rateAt_cases v k with h | h <;> norm_num [h]
  have hm := fun v => heatCost_aemeasurable Hd hh (hα1 v) (hα2 v) ha0 hab
  let c := 5 / 3 * constD * constA ^ 2
  let B := 28 * (2 * Real.sqrt 2 * (1 + Real.sqrt (2 / Real.pi))) * ∑ v, Hd.nCube v
  have hc : 0 ≤ c := by have := constD_spec.1; dsimp [c]; positivity
  have hB : 0 ≤ B := by
    dsimp [B, HeatData.nCube]
    positivity
  have he : ∀ v, ∫⁻ z, heatCost Hd (rateAt v) z
      ∂((volume.restrict (Set.Ioc a b)).prod volume) ≤ ENNReal.ofReal B := fun v =>
    heatCost_interval_bound Hd hk hu hh (rateAt_cases v) (rateAt_sum v) ha hab
  have hb : ENNReal.ofReal ‖gridGaussianForm Hd a b‖ ≤
      ENNReal.ofReal c * ∑ _v : Fin 3, ENNReal.ofReal B := by
    rw [ofReal_norm, gridGaussianForm_eq Hd hh ha0 hab]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    calc
      ∫⁻ s in Set.Ioc a b,
          ‖((1 / s : ℝ) : ℂ) * ∫ q : Fin 2 → ℝ, Hd.baseTrace 3 (planePt q) s‖ₑ ≤
          ∫⁻ s in Set.Ioc a b, ENNReal.ofReal c *
            ∑ v, ∫⁻ p, heatCost Hd (rateAt v) (s, p) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact heatTrace_bound Hd hh (ha0.trans hs.1)
      _ = ENNReal.ofReal c * ∑ v, ∫⁻ z, heatCost Hd (rateAt v) z
          ∂((volume.restrict (Set.Ioc a b)).prod volume) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum']
        · congr 1
          exact Finset.sum_congr rfl fun v _ => (lintegral_prod _ (hm v)).symm
        · intro v _
          exact (hm v).lintegral_prod_right'
      _ ≤ _ := mul_le_mul' le_rfl (Finset.sum_le_sum fun v _ => he v)
  have heq : ENNReal.ofReal c * ∑ _v : Fin 3, ENNReal.ofReal B =
      ENNReal.ofReal (heatBoundConstant * ∑ v, Hd.nCube v) := by
    rw [Fin.sum_univ_three, ← ENNReal.ofReal_add hB hB,
      ← ENNReal.ofReal_add (add_nonneg hB hB) hB, ← ENNReal.ofReal_mul hc]
    congr 1
    dsimp [c, B, heatBoundConstant]
    ring
  rw [heq] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by
    apply mul_nonneg heatBoundConstant_nonneg
    exact Finset.sum_nonneg fun v _ => by dsimp [HeatData.nCube]; positivity)).mp hb
end Auto
