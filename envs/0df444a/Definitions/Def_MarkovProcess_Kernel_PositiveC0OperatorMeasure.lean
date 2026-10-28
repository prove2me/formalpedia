-- Prove2me | Definitions.Def_MarkovProcess_Kernel_PositiveC0OperatorMeasure
-- name    : MarkovProcess_Kernel_PositiveC0OperatorMeasure
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T11:55:39.424402+00:00
-- url     : https://prove2.me/theorems/3b09578a-5d84-4693-b12f-6f3f81a86f90
-- title:
--   MarkovProcess definitions: Kernel.PositiveC0OperatorMeasure
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Kernel.PositiveC0OperatorMeasure`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/PositiveC0OperatorMeasure.lean#L1-L119

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Pointwise Riesz measures of positive operators on `C₀`

A positive continuous linear operator on real continuous functions vanishing at infinity gives,
after evaluation at a point, a positive linear functional on compactly supported continuous
functions. The real Riesz--Markov--Kakutani theorem represents this functional by a regular,
locally finite measure.

This file makes only this pointwise construction. It does not prove that the measures depend
measurably on the evaluation point, have bounded total mass, form a kernel, or satisfy any
semigroup or stochastic-process law.
-/

open CompactlySupported MeasureTheory
open scoped ZeroAtInfty

namespace MarkovProcess

variable {α : Type*} [TopologicalSpace α]





namespace PositiveC0OperatorMeasure

/-- Pointwise preservation of nonnegative functions by an operator on `C₀(α, ℝ)`. -/
def IsPositive (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ)) : Prop :=
  ∀ f : C₀(α, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T f x



/-- The canonical real-linear inclusion of compactly supported continuous functions into `C₀`. -/
noncomputable def compactlySupportedToC0LinearMap : C_c(α, ℝ) →ₗ[ℝ] C₀(α, ℝ) where
  toFun f := f
  map_add' f g := by
    ext x
    rfl
  map_smul' c f := by
    ext x
    rfl



variable (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ)) (hT : IsPositive T)

/-- Evaluation at `x` after applying `T`, restricted from `C₀(α, ℝ)` to compactly supported
continuous functions, as a positive linear functional. -/
noncomputable def functional (x : α) : C_c(α, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f ↦ T (compactlySupportedToC0LinearMap f) x
      map_add' := by
        intro f g
        rw [map_add, map_add]
        rfl
      map_smul' := by
        intro c f
        rw [map_smul, map_smul]
        rfl }
    fun f hf ↦ hT (compactlySupportedToC0LinearMap f) (fun y ↦ hf y) x



variable [T2Space α] [LocallyCompactSpace α] [MeasurableSpace α] [BorelSpace α]

/-- The regular Riesz measure representing point evaluation after applying `T`. -/
noncomputable def measure (x : α) : Measure α :=
  RealRMK.rieszMeasure (functional T hT x)

instance regular_measure (x : α) : (measure T hT x).Regular :=
  RealRMK.regular_rieszMeasure (functional T hT x)

instance isFiniteMeasureOnCompacts_measure (x : α) :
    IsFiniteMeasureOnCompacts (measure T hT x) :=
  inferInstance



end PositiveC0OperatorMeasure

end MarkovProcess


