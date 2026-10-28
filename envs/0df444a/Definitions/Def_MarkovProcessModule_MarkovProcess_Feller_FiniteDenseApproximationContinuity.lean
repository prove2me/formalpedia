-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Feller_FiniteDenseApproximationContinuity
-- name    : MarkovProcessModule_MarkovProcess_Feller_FiniteDenseApproximationContinuity
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T20:56:21.723229+00:00
-- url     : https://prove2.me/theorems/e20245d7-06a5-4fad-942f-847be43455fa
-- title:
--   MarkovProcess.Feller.FiniteDenseApproximationContinuity
-- statement:
--   # Feller continuity of finite dense approximations
--
--   This file proves compact-test convergence of the finite laws obtained by simultaneously
--   approximating a finite set of nonnegative-real times by dense times. Both the approximating and
--   limiting kernels are transported through the same ordered-coordinate homeomorphism, after which
--   the finite-time Feller continuity theorem applies directly.
--
--   This is finite-dimensional infrastructure. No path-space Markov property is asserted here; the
--   Markov and strong Markov statements are in `MarkovProcess/Main.lean`.
--
--   Complete pinned Lean module MarkovProcess.Feller.FiniteDenseApproximationContinuity by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Feller/FiniteDenseApproximationContinuity.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Feller_FiniteTimeCompactTestContinuity
import Definitions.Def_MarkovProcessModule_MarkovProcess_Time_FiniteDenseApproximationOrdered
import Definitions.Def_MarkovProcessModule_MarkovProcess_FiniteTime_FiniteSetKernelCompactTestTransport

/-!
# Feller continuity of finite dense approximations

This file proves compact-test convergence of the finite laws obtained by simultaneously
approximating a finite set of nonnegative-real times by dense times. Both the approximating and
limiting kernels are transported through the same ordered-coordinate homeomorphism, after which
the finite-time Feller continuity theorem applies directly.

This is finite-dimensional infrastructure. No path-space Markov property is asserted here; the
Markov and strong Markov statements are in `MarkovProcess/Main.lean`.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal CompactlySupported

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

/-- Compact-test integrals against finite dense approximations converge to the corresponding
finite-set-kernel integral under simultaneous coordinatewise convergence of the times. -/
theorem IsFellerKernelSemigroup.tendsto_integral_compactlySupported_finiteDenseApproximationKernel
    {P : SubMarkovKernelSemigroup alpha} (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) {I : Finset NNReal} (q : ℕ → I ↪o DenseTime)
    (hq : ∀ t, Tendsto
      (fun k ↦ DenseTime.castOrderEmbedding (q k t)) atTop (nhds (t : NNReal)))
    (f : C_c(I → alpha, ℝ)) (x : alpha) :
    Tendsto
      (fun k ↦ ∫ y, f y ∂finiteDenseApproximationKernel P (q k) x)
      atTop (nhds (∫ y, f y ∂finiteSetKernel P I x)) := by
  have htime : ∀ i, Tendsto
      (fun k ↦ finiteDenseApproximationOrderedTimes (q k) i) atTop
        (nhds (finiteSetTimes I i)) :=
    tendsto_finiteDenseApproximationOrderedTimes q hq
  have h := hFeller.tendsto_integral_compactlySupported_finiteTimeKernel
    hP htime (pullbackFiniteSetCompactTest I f) x
  have happrox (k : ℕ) :
      (∫ y, f y ∂finiteDenseApproximationKernel P (q k) x) =
        ∫ path, pullbackFiniteSetCompactTest I f path
          ∂finiteTimeKernel P (finiteDenseApproximationOrderedTimes (q k)) x := by
    rw [finiteDenseApproximationKernel_eq_map_finiteTimeKernel P hP (q k),
      Kernel.map_apply _ (measurable_orderedPathToFiniteSet I)]
    exact integral_map_orderedPathToFiniteSet I f _
  rw [show (fun k ↦ ∫ y, f y ∂finiteDenseApproximationKernel P (q k) x) =
      (fun k ↦ ∫ path, pullbackFiniteSetCompactTest I f path
        ∂finiteTimeKernel P (finiteDenseApproximationOrderedTimes (q k)) x) from
      funext happrox,
    integral_finiteSetKernel_eq_integral_pullbackFiniteSetCompactTest P I f x]
  exact h

end MarkovProcess.SubMarkovKernelSemigroup


