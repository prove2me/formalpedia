-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_FiniteTime_KernelShift
-- name    : MarkovProcessModule_MarkovProcess_FiniteTime_KernelShift
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:47:01.681049+00:00
-- url     : https://prove2.me/theorems/d450cb94-7eb3-424f-b56e-64d1fc1f1c99
-- title:
--   MarkovProcess.FiniteTime.KernelShift
-- statement:
--   # Translation of finite-time kernels
--
--   This file proves the finite-dimensional translation identity for a conservative transition-kernel
--   semigroup. It is ordinary kernel infrastructure and makes no path-space or process-existence claim.
--
--   Complete pinned Lean module MarkovProcess.FiniteTime.KernelShift by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/KernelShift.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_FiniteTime_Kernel
import Mathlib.Probability.Kernel.Composition.KernelLemmas

/-!
# Translation of finite-time kernels

This file proves the finite-dimensional translation identity for a conservative transition-kernel
semigroup. It is ordinary kernel infrastructure and makes no path-space or process-existence claim.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

variable {W X Y Z : Type*}
variable [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

private theorem compProd_prodMkLeft_comp (κ : Kernel X Y) (η : Kernel Y Z)
    (ξ : Kernel W X) [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel ξ] :
    (κ.comp ξ) ⊗ₖ Kernel.prodMkLeft W η = (κ ⊗ₖ Kernel.prodMkLeft X η).comp ξ := by
  rw [Kernel.compProd_prodMkLeft_eq_comp, Kernel.compProd_prodMkLeft_eq_comp,
    Kernel.comp_assoc]

namespace IsConservative

variable {α : Type*} [MeasurableSpace α]

/-- Translating all observation times is the same as first evolving for the translation amount. -/
theorem finiteTimeKernel_translate (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (s : NNReal) {n : ℕ} (times : FiniteOrderedTimes n) :
    finiteTimeKernel P (times.translate s) = (finiteTimeKernel P times).comp (P s) := by
  induction n with
  | zero =>
      let : IsMarkovKernel (P s) := hP.isMarkovKernel s
      rw [finiteTimeKernel_zero, finiteTimeKernel_zero, Kernel.const_comp']
  | succ n ih =>
      let : IsFiniteKernel (P s) := (P.isSubMarkovKernel s).isFiniteKernel
      let : IsFiniteKernel (P (times 0)) :=
        (P.isSubMarkovKernel (times 0)).isFiniteKernel
      let : IsMarkovKernel (finiteTimeKernel P times.relativeTail) :=
        hP.isMarkovKernel_finiteTimeKernel P times.relativeTail
      rw [finiteTimeKernel_succ, finiteTimeKernel_succ]
      simp only [FiniteOrderedTimes.translate_apply, FiniteOrderedTimes.relativeTail_translate]
      rw [P.add s (times 0), Kernel.mapOfMeasurable_eq_map,
        Kernel.mapOfMeasurable_eq_map, compProd_prodMkLeft_comp, Kernel.map_comp]

end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess


