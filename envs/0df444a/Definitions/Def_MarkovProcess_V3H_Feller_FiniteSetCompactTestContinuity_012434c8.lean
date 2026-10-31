-- Prove2me | Definitions.Def_MarkovProcess_V3H_Feller_FiniteSetCompactTestContinuity_012434c8
-- name    : MarkovProcess_V3H_Feller_FiniteSetCompactTestContinuity_012434c8
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:45:39.017087+00:00
-- url     : https://prove2.me/theorems/85142f59-b115-41f4-93e2-55733cb45261
-- title:
--   MarkovProcess: MarkovProcess_V3H_Feller_FiniteSetCompactTestContinuity_012434c8
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Feller_FiniteTimeJointCompactTestContinuity_c5428240
import Definitions.Def_MarkovProcess_V3H_Feller_Semigroup_2cfe612a
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelCompactTestTransport_3904fd05
import Definitions.Def_MarkovProcess_V3H_FiniteTime_Kernel_7ce8d73d
import Definitions.Def_MarkovProcess_V3H_FiniteTime_ProjectiveFamily_1eff0efa
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

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


