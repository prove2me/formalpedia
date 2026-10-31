-- Prove2me | Definitions.Def_MarkovProcess_V3H_Parameterized_DenseTimePrefixKernel_12387c59
-- name    : MarkovProcess_V3H_Parameterized_DenseTimePrefixKernel_12387c59
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:40:21.790357+00:00
-- url     : https://prove2.me/theorems/95ca2639-b815-4398-b97d-e55cd577d984
-- title:
--   MarkovProcess: MarkovProcess_V3H_Parameterized_DenseTimePrefixKernel_12387c59
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_PrefixKernel_a192bbea
import Definitions.Def_MarkovProcess_V3H_FiniteTime_ProjectiveFamily_1eff0efa
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Parameterized_FiniteTimeProjectiveFamily_8428346b
import Definitions.Def_MarkovProcess_V3H_Parameterized_Semigroup_5f8b28ce
import Definitions.Def_MarkovProcess_V3H_Time_FiniteOrderedTimes_717796dd
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
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
# Parameterized kernels on finite prefixes of a countable time enumeration

This file constructs jointly measurable kernels on the first `n` points of an arbitrary
enumeration. Coordinates remain in enumeration order; the enumeration need not be monotone in
physical time. Fiberwise conservativity is used only for Markovness and prefix consistency.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

noncomputable section

variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]

/-- The jointly measurable kernel on the first `n` enumerated physical times. -/
def parameterizedDenseTimePrefixKernel
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (e : ℕ ≃ D)
    (ι : D ↪ NNReal) (n : ℕ) : Kernel (Theta × alpha) (Fin n → alpha) :=
  Kernel.mapOfMeasurable
    (P.parameterizedFiniteSetKernel
      (SubMarkovKernelSemigroup.denseTimePhysicalPrefix e ι n))
    (SubMarkovKernelSemigroup.denseTimePrefixReindex e ι n)
    (SubMarkovKernelSemigroup.measurable_denseTimePrefixReindex e ι n)

/-- The parameterized prefix kernel agrees with the ordinary kernel map. -/
theorem parameterizedDenseTimePrefixKernel_eq_map
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (e : ℕ ≃ D)
    (ι : D ↪ NNReal) (n : ℕ) :
    P.parameterizedDenseTimePrefixKernel e ι n =
      (P.parameterizedFiniteSetKernel
        (SubMarkovKernelSemigroup.denseTimePhysicalPrefix e ι n)).map
          (SubMarkovKernelSemigroup.denseTimePrefixReindex e ι n) :=
  Kernel.mapOfMeasurable_eq_map _
    (SubMarkovKernelSemigroup.measurable_denseTimePrefixReindex e ι n)

/-- At a fixed parameter and start, the prefix kernel is the ordinary prefix kernel. -/
theorem parameterizedDenseTimePrefixKernel_apply
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (e : ℕ ≃ D)
    (ι : D ↪ NNReal) (n : ℕ) (theta : Theta) (x : alpha) :
    P.parameterizedDenseTimePrefixKernel e ι n (theta, x) =
      (P.toSubMarkovKernelSemigroup theta).denseTimePrefixKernel e ι n x := by
  rw [parameterizedDenseTimePrefixKernel_eq_map,
    Kernel.map_apply _
      (SubMarkovKernelSemigroup.measurable_denseTimePrefixReindex e ι n),
    parameterizedFiniteSetKernel_apply,
    SubMarkovKernelSemigroup.denseTimePrefixKernel_eq_map,
    Kernel.map_apply _
      (SubMarkovKernelSemigroup.measurable_denseTimePrefixReindex e ι n)]

/-- Fiberwise conservativity makes each parameterized prefix kernel Markov. -/
theorem isMarkovKernel_parameterizedDenseTimePrefixKernel
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    IsMarkovKernel (P.parameterizedDenseTimePrefixKernel e ι n) := by
  rw [parameterizedDenseTimePrefixKernel_eq_map]
  let : IsMarkovKernel
      (P.parameterizedFiniteSetKernel
        (SubMarkovKernelSemigroup.denseTimePhysicalPrefix e ι n)) :=
    P.isMarkovKernel_parameterizedFiniteSetKernel hP _
  exact Kernel.IsMarkovKernel.map _
    (SubMarkovKernelSemigroup.measurable_denseTimePrefixReindex e ι n)

/-- Parameterized prefix kernels restrict exactly to every earlier enumeration prefix. -/
theorem p2m_embedded_7534060ff52e2426
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) {m n : ℕ} (h : m ≤ n) :
    P.parameterizedDenseTimePrefixKernel e ι m =
      (P.parameterizedDenseTimePrefixKernel e ι n).map
        (FiniteOrderedTimes.restrictPath (Fin.castLEOrderEmb h)) := by
  apply Kernel.ext
  intro q
  obtain ⟨theta, x⟩ := q
  rw [Kernel.map_apply _
      (FiniteOrderedTimes.measurable_restrictPath (Fin.castLEOrderEmb h)),
    parameterizedDenseTimePrefixKernel_apply,
    parameterizedDenseTimePrefixKernel_apply]
  have hrestrict := congrArg (fun K : Kernel alpha (Fin m → alpha) ↦ K x)
    ((hP theta).denseTimePrefixKernel_map_restrictPath
      (P.toSubMarkovKernelSemigroup theta) e ι h)
  change (P.toSubMarkovKernelSemigroup theta).denseTimePrefixKernel e ι m x =
    ((P.toSubMarkovKernelSemigroup theta).denseTimePrefixKernel e ι n).map
      (FiniteOrderedTimes.restrictPath (Fin.castLEOrderEmb h)) x at hrestrict
  rw [Kernel.map_apply _
    (FiniteOrderedTimes.measurable_restrictPath (Fin.castLEOrderEmb h))] at hrestrict
  exact hrestrict

end
end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess


