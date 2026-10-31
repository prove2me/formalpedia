-- Prove2me | Definitions.Def_MarkovProcess_V3H_Parameterized_FiniteTimeProjectiveFamily_8428346b
-- name    : MarkovProcess_V3H_Parameterized_FiniteTimeProjectiveFamily_8428346b
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:38:27.092579+00:00
-- url     : https://prove2.me/theorems/20398231-8974-4b67-8afa-22e8c2856226
-- title:
--   MarkovProcess: MarkovProcess_V3H_Parameterized_FiniteTimeProjectiveFamily_8428346b
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_FiniteTime_Kernel_7ce8d73d
import Definitions.Def_MarkovProcess_V3H_FiniteTime_ProjectiveFamily_1eff0efa
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Parameterized_FiniteTimeKernel_da0af7ef
import Definitions.Def_MarkovProcess_V3H_Parameterized_Semigroup_5f8b28ce
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Parameterized finite-set finite-time kernels

This file reindexes parameterized finite-time kernels by finite sets of times. It proves exact
agreement with the ordinary finite-set kernel at every fixed parameter and starting state, and
derives projectivity under fiberwise conservativity. It does not construct a projective-limit
measure or a stochastic process.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]

/-- The jointly measurable finite-time kernel indexed by a finite set of times. -/
noncomputable def parameterizedFiniteSetKernel
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (I : Finset NNReal) :
    Kernel (Theta × alpha) (I → alpha) :=
  Kernel.mapOfMeasurable
    (P.parameterizedFiniteTimeKernel (SubMarkovKernelSemigroup.finiteSetTimes I))
    (SubMarkovKernelSemigroup.orderedPathToFiniteSet I)
    (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I)

/-- The parameterized finite-set kernel agrees with the ordinary kernel map. -/
theorem parameterizedFiniteSetKernel_eq_map
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (I : Finset NNReal) :
    P.parameterizedFiniteSetKernel I =
      (P.parameterizedFiniteTimeKernel
        (SubMarkovKernelSemigroup.finiteSetTimes I)).map
          (SubMarkovKernelSemigroup.orderedPathToFiniteSet I) :=
  Kernel.mapOfMeasurable_eq_map _
    (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I)

/-- At a fixed parameter and start, the parameterized finite-set kernel is the ordinary one. -/
theorem parameterizedFiniteSetKernel_apply
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (I : Finset NNReal)
    (theta : Theta) (x : alpha) :
    P.parameterizedFiniteSetKernel I (theta, x) =
      (P.toSubMarkovKernelSemigroup theta).finiteSetKernel I x := by
  rw [parameterizedFiniteSetKernel_eq_map,
    Kernel.map_apply _ (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I),
    _root_.MarkovProcess.ParameterizedSubMarkovKernelSemigroup.p2m_embedded_b37d2d36908b1e6a,
    SubMarkovKernelSemigroup.finiteSetKernel_eq_map,
    Kernel.map_apply _ (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I)]

/-- Fiberwise conservativity makes every parameterized finite-set kernel Markov. -/
theorem isMarkovKernel_parameterizedFiniteSetKernel
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (I : Finset NNReal) : IsMarkovKernel (P.parameterizedFiniteSetKernel I) := by
  rw [parameterizedFiniteSetKernel_eq_map]
  let : IsMarkovKernel
      (P.parameterizedFiniteTimeKernel (SubMarkovKernelSemigroup.finiteSetTimes I)) :=
    P.p2m_embedded_59e0ef7480dbc6d8 hP
      (SubMarkovKernelSemigroup.finiteSetTimes I)
  exact Kernel.IsMarkovKernel.map _
    (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I)





end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess


