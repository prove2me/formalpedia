-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Feller_FiniteSetConvergence
-- name    : MarkovProcessModule_MarkovProcess_Feller_FiniteSetConvergence
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T20:17:48.48741+00:00
-- url     : https://prove2.me/theorems/8cc87f5e-636a-4787-91df-29294e32a6fa
-- title:
--   MarkovProcess.Feller.FiniteSetConvergence
-- statement:
--   # Convergence of the finite-dimensional laws of Feller semigroups
--
--   The finite-time results of `Feller/FiniteTimeConvergence.lean`, reindexed by a finite set of
--   times.  For conservative Feller kernel semigroups whose `C₀` semigroups converge strongly, the
--   finite-set laws converge against every compactly supported continuous test, uniformly in the
--   starting point; and, at a fixed starting point, against every bounded continuous test, which is
--   weak convergence of the finite-dimensional distributions.
--
--   The second statement cannot be uniform in the starting point: it uses the tightness of the
--   limiting law at that point (`Kernel/WeakConvergence.lean`), and on a noncompact state space the
--   finite-dimensional laws of a family of starting points escaping to infinity are not tight.
--
--   Main results: `tendstoUniformly_integral_compactlySupported_finiteSetKernel`,
--   `tendsto_integral_boundedContinuous_finiteSetKernel`.
--
--   The set of observation times is fixed; nothing is asserted about joint convergence in the times
--   and the semigroups.
--
--   Complete pinned Lean module MarkovProcess.Feller.FiniteSetConvergence by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Feller/FiniteSetConvergence.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Feller_FiniteTimeConvergence
import Definitions.Def_MarkovProcessModule_MarkovProcess_FiniteTime_FiniteSetKernelCompactTestTransport
import Definitions.Def_MarkovProcessModule_MarkovProcess_Kernel_WeakConvergence

/-!
# Convergence of the finite-dimensional laws of Feller semigroups

The finite-time results of `Feller/FiniteTimeConvergence.lean`, reindexed by a finite set of
times.  For conservative Feller kernel semigroups whose `C₀` semigroups converge strongly, the
finite-set laws converge against every compactly supported continuous test, uniformly in the
starting point; and, at a fixed starting point, against every bounded continuous test, which is
weak convergence of the finite-dimensional distributions.

The second statement cannot be uniform in the starting point: it uses the tightness of the
limiting law at that point (`Kernel/WeakConvergence.lean`), and on a noncompact state space the
finite-dimensional laws of a family of starting points escaping to infinity are not tight.

Main results: `tendstoUniformly_integral_compactlySupported_finiteSetKernel`,
`tendsto_integral_boundedContinuous_finiteSetKernel`.

The set of observation times is fixed; nothing is asserted about joint convergence in the times
and the semigroups.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BoundedContinuousFunction CompactlySupported NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

section CompactTest

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha] [SecondCountableTopology alpha]
variable {iota : Type*} {l : Filter iota}
variable {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}

/-- **Uniform convergence of the finite-set laws against compactly supported tests.** -/
theorem tendstoUniformly_integral_compactlySupported_finiteSetKernel
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hPc : ∀ i, (P i).IsConservative)
    (hQ : Q.IsFellerKernelSemigroup) (hQc : Q.IsConservative)
    (hconv : ∀ (t : NNReal) (f : C₀(alpha, ℝ)),
      Tendsto (fun i ↦ (hP i).c0Semigroup t f) l (nhds (hQ.c0Semigroup t f)))
    (I : Finset NNReal) (f : C_c(I → alpha, ℝ)) :
    TendstoUniformly (fun i x ↦ ∫ path, f path ∂finiteSetKernel (P i) I x)
      (fun x ↦ ∫ path, f path ∂finiteSetKernel Q I x) l := by
  have h := tendstoUniformly_integral_compactlySupported_finiteTimeKernel hP hPc hQ hQc hconv
    (finiteSetTimes I) (pullbackFiniteSetCompactTest I f)
  simpa only [integral_finiteSetKernel_eq_integral_pullbackFiniteSetCompactTest] using h

end CompactTest

section BoundedContinuousTest

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [SecondCountableTopology alpha] [LocallyCompactSpace alpha]
variable {iota : Type*} {l : Filter iota}
variable {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}

/-- **Weak convergence of the finite-dimensional laws.**  At every starting point, the finite-set
law of `P i` converges to that of `Q` against every bounded continuous test function. -/
theorem tendsto_integral_boundedContinuous_finiteSetKernel
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hPc : ∀ i, (P i).IsConservative)
    (hQ : Q.IsFellerKernelSemigroup) (hQc : Q.IsConservative)
    (hconv : ∀ (t : NNReal) (f : C₀(alpha, ℝ)),
      Tendsto (fun i ↦ (hP i).c0Semigroup t f) l (nhds (hQ.c0Semigroup t f)))
    (I : Finset NNReal) (f : (I → alpha) →ᵇ ℝ) (x : alpha) :
    Tendsto (fun i ↦ ∫ path, f path ∂finiteSetKernel (P i) I x) l
      (nhds (∫ path, f path ∂finiteSetKernel Q I x)) := by
  let : ∀ i, IsMarkovKernel (finiteSetKernel (P i) I) := fun i ↦
    (hPc i).isMarkovKernel_finiteSetKernel (P i) I
  let : IsMarkovKernel (finiteSetKernel Q I) := hQc.isMarkovKernel_finiteSetKernel Q I
  let : ∀ i, IsProbabilityMeasure (finiteSetKernel (P i) I x) := fun i ↦
    IsMarkovKernel.isProbabilityMeasure x
  let : IsProbabilityMeasure (finiteSetKernel Q I x) := IsMarkovKernel.isProbabilityMeasure x
  refine tendsto_integral_boundedContinuous_of_tendsto_compactlySupported
    (fun i ↦ finiteSetKernel (P i) I x) (finiteSetKernel Q I x) (fun g ↦ ?_) f
  exact (tendstoUniformly_integral_compactlySupported_finiteSetKernel hP hPc hQ hQc hconv
    I g).tendsto_at x

end BoundedContinuousTest

end MarkovProcess.SubMarkovKernelSemigroup


