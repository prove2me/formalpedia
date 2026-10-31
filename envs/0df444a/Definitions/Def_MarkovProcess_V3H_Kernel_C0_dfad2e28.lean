-- Prove2me | Definitions.Def_MarkovProcess_V3H_Kernel_C0_dfad2e28
-- name    : MarkovProcess_V3H_Kernel_C0_dfad2e28
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:32:16.93387+00:00
-- url     : https://prove2.me/theorems/877c9ce6-31e6-4f48-b6a3-0bc9fc7eb105
-- title:
--   MarkovProcess: MarkovProcess_V3H_Kernel_C0_dfad2e28
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_Basic_264434f5
import Definitions.Def_MarkovProcess_V3H_Kernel_Integral_2b459584
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Kernel operators on continuous functions vanishing at infinity

This file records the spatial `C₀` property of a sub-Markov kernel semigroup and packages its
raw integral as a contractive continuous linear map on `C₀(α, ℝ)`.  It makes no assertion about
continuity in time or the existence of an associated stochastic process.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal ZeroAtInfty

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]

/-- A kernel semigroup maps `C₀(α, ℝ)` into itself when its raw kernel integral is continuous
and vanishes at infinity at every time. -/
def MapsC0 (P : SubMarkovKernelSemigroup α) : Prop :=
  ∀ t (f : C₀(α, ℝ)),
    Continuous (kernelIntegral (P t) f) ∧
      Tendsto (kernelIntegral (P t) f) (cocompact α) (nhds 0)

variable (P : SubMarkovKernelSemigroup α) (hC0 : P.MapsC0)

/-- The exact `C₀` representative obtained by integrating against `P t`. -/
noncomputable def c0KernelIntegral (t : NNReal) (f : C₀(α, ℝ)) : C₀(α, ℝ) where
  toFun := kernelIntegral (P t) f
  continuous_toFun := (hC0 t f).1
  zero_at_infty' := (hC0 t f).2

@[simp]
theorem c0KernelIntegral_apply (t : NNReal) (f : C₀(α, ℝ)) (x : α) :
    P.c0KernelIntegral hC0 t f x = kernelIntegral (P t) f x :=
  rfl

variable [BorelSpace α]

private theorem integrable_fiber (t : NNReal) (f : C₀(α, ℝ)) (x : α) :
    Integrable f (P t x) := by
  let : IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  exact f.toBCF.integrable (P t x)

private theorem norm_c0KernelIntegral_le (t : NNReal) (f : C₀(α, ℝ)) :
    ‖P.c0KernelIntegral hC0 t f‖ ≤ ‖f‖ := by
  let : IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).2
  intro x
  calc
    ‖P.c0KernelIntegral hC0 t f x‖
        ≤ (P t x).real Set.univ * ‖f.toBCF‖ :=
      f.toBCF.norm_integral_le_mul_norm (P t x)
    _ ≤ 1 * ‖f.toBCF‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [Measure.real_def]
      exact ENNReal.toReal_mono ENNReal.one_ne_top
        ((P.isSubMarkovKernel t) x)
    _ = ‖f‖ := by
      rw [one_mul, ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]

/-- The kernel integral as a contraction on real continuous functions vanishing at infinity. -/
noncomputable def c0Operator (t : NNReal) : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ) :=
  LinearMap.mkContinuous
    { toFun := P.c0KernelIntegral hC0 t
      map_add' := fun f g ↦ by
        apply ZeroAtInftyContinuousMap.ext
        intro x
        change ∫ y, (f y + g y) ∂P t x = (∫ y, f y ∂P t x) + ∫ y, g y ∂P t x
        exact integral_add (P.integrable_fiber t f x) (P.integrable_fiber t g x)
      map_smul' := fun c f ↦ by
        apply ZeroAtInftyContinuousMap.ext
        intro x
        change ∫ y, c * f y ∂P t x = c * ∫ y, f y ∂P t x
        simpa only [smul_eq_mul] using
          (integral_smul c (fun y ↦ f y) :
            (∫ y, c • f y ∂P t x) = c • ∫ y, f y ∂P t x) }
    1 fun f ↦ by
      rw [one_mul]
      exact P.norm_c0KernelIntegral_le hC0 t f

@[simp]
theorem c0Operator_apply (t : NNReal) (f : C₀(α, ℝ)) (x : α) :
    P.c0Operator hC0 t f x = kernelIntegral (P t) f x :=
  rfl

/-- At time zero the `C₀` kernel operator is the identity. -/
@[simp]
theorem c0Operator_zero :
    P.c0Operator hC0 0 = ContinuousLinearMap.id ℝ C₀(α, ℝ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ZeroAtInftyContinuousMap.ext
  intro x
  rw [c0Operator_apply, P.zero]
  exact integral_dirac' f x f.continuous.stronglyMeasurable

/-- Kernel composition gives the algebraic semigroup law on `C₀`. -/
@[simp]
theorem c0Operator_add (s t : NNReal) :
    P.c0Operator hC0 (s + t) =
      (P.c0Operator hC0 s).comp (P.c0Operator hC0 t) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ZeroAtInftyContinuousMap.ext
  intro x
  change kernelIntegral (P (s + t)) f x =
    kernelIntegral (P s) (kernelIntegral (P t) f) x
  have hf := P.integrable_fiber (s + t) f x
  rw [P.add] at hf ⊢
  exact Kernel.integral_comp hf

/-- Every time slice of the `C₀` kernel operator has operator norm at most one. -/
theorem norm_c0Operator_le (t : NNReal) : ‖P.c0Operator hC0 t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using! P.norm_c0KernelIntegral_le hC0 t f



end SubMarkovKernelSemigroup

end MarkovProcess


