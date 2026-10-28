-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Feller_FiniteTimeContinuityBase
-- name    : MarkovProcessModule_MarkovProcess_Feller_FiniteTimeContinuityBase
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:57:26.102748+00:00
-- url     : https://prove2.me/theorems/7fc0f717-2a93-47e9-920b-cdc3ac39d46f
-- title:
--   MarkovProcess.Feller.FiniteTimeContinuityBase
-- statement:
--   # Singleton finite-time Feller continuity
--
--   For a one-coordinate finite-time kernel, evaluation at the unique coordinate recovers the
--   transition kernel at that time.  Feller continuity therefore gives convergence of its `C₀` test
--   integrals as the observation time varies.  This is the base case for a recursive finite-time
--   continuity argument; no higher-dimensional continuity is asserted here.
--
--   Complete pinned Lean module MarkovProcess.Feller.FiniteTimeContinuityBase by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Feller/FiniteTimeContinuityBase.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Feller_FiniteTimeKernelContinuity
import Definitions.Def_MarkovProcessModule_MarkovProcess_FiniteTime_Kernel

/-!
# Singleton finite-time Feller continuity

For a one-coordinate finite-time kernel, evaluation at the unique coordinate recovers the
transition kernel at that time.  Feller continuity therefore gives convergence of its `C₀` test
integrals as the observation time varies.  This is the base case for a recursive finite-time
continuity argument; no higher-dimensional continuity is asserted here.
-/

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

variable {alpha X : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

/-- Kernel integrals of `C₀` tests against singleton finite-time laws vary continuously with the
unique observation time. -/
theorem IsFellerKernelSemigroup.tendsto_kernelIntegral_finiteTimeKernel_one_map_eval
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    {l : Filter X} {times : X → FiniteOrderedTimes 1}
    {times0 : FiniteOrderedTimes 1}
    (ht : Tendsto (fun a ↦ times a 0) l (nhds (times0 0)))
    (f : C₀(alpha, ℝ)) (x : alpha) :
    Tendsto (fun a ↦ kernelIntegral
        ((finiteTimeKernel P (times a)).map (fun path ↦ path 0)) f x)
      l (nhds (kernelIntegral
        ((finiteTimeKernel P times0).map (fun path ↦ path 0)) f x)) := by
  simp_rw [finiteTimeKernel_one_map_eval]
  exact hP.tendsto_kernelIntegral_c0 ht tendsto_const_nhds x

end SubMarkovKernelSemigroup
end MarkovProcess


