-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Feller_FiniteSetCompactTestContinuity
-- name    : MarkovProcessModule_MarkovProcess_Feller_FiniteSetCompactTestContinuity
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T20:26:03.743766+00:00
-- url     : https://prove2.me/theorems/4d44394f-322d-4be2-bb7c-3dbba6a8e7ed
-- title:
--   MarkovProcess.Feller.FiniteSetCompactTestContinuity
-- statement:
--   # Continuity of finite-set compact-test integrals
--
--   Compact-test integrals against a conservative Feller semigroup's finite-set kernel vary
--   continuously with the starting point. The proof transports the test to increasing coordinates
--   and applies fixed-time finite-kernel continuity. The empty finite set is included without a
--   separate nonemptiness assumption.
--
--   This is finite-dimensional analytic infrastructure; no statement about path space is proved
--   here.  The continuous-path process is built in `Trajectory/`.
--
--   Complete pinned Lean module MarkovProcess.Feller.FiniteSetCompactTestContinuity by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Feller/FiniteSetCompactTestContinuity.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Feller_FiniteTimeJointCompactTestContinuity
import Definitions.Def_MarkovProcessModule_MarkovProcess_FiniteTime_FiniteSetKernelCompactTestTransport

/-!
# Continuity of finite-set compact-test integrals

Compact-test integrals against a conservative Feller semigroup's finite-set kernel vary
continuously with the starting point. The proof transports the test to increasing coordinates
and applies fixed-time finite-kernel continuity. The empty finite set is included without a
separate nonemptiness assumption.

This is finite-dimensional analytic infrastructure; no statement about path space is proved
here.  The continuous-path process is built in `Trajectory/`.
-/

open MeasureTheory
open scoped NNReal CompactlySupported

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

/-- A compact-test integral against a finite-set kernel is continuous in the starting point. -/
theorem IsFellerKernelSemigroup.continuous_integral_compactlySupported_finiteSetKernel
    {P : SubMarkovKernelSemigroup alpha} (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (I : Finset NNReal) (f : C_c(I → alpha, ℝ)) :
    Continuous fun x ↦ ∫ path, f path ∂finiteSetKernel P I x := by
  have h := hFeller.continuous_integral_compactlySupported_finiteTimeKernel hP
    (finiteSetTimes I) (pullbackFiniteSetCompactTest I f)
  simpa only [integral_finiteSetKernel_eq_integral_pullbackFiniteSetCompactTest P I f]
    using h

end MarkovProcess.SubMarkovKernelSemigroup


