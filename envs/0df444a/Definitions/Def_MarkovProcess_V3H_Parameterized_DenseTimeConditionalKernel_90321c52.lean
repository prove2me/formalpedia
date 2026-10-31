-- Prove2me | Definitions.Def_MarkovProcess_V3H_Parameterized_DenseTimeConditionalKernel_90321c52
-- name    : MarkovProcess_V3H_Parameterized_DenseTimeConditionalKernel_90321c52
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:45:39.825747+00:00
-- url     : https://prove2.me/theorems/780c7583-22a2-42e0-83b6-89083e719b58
-- title:
--   MarkovProcess: MarkovProcess_V3H_Parameterized_DenseTimeConditionalKernel_90321c52
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Parameterized_DenseTimePrefixKernel_12387c59
import Definitions.Def_MarkovProcess_V3H_Parameterized_Semigroup_5f8b28ce
import Definitions.Def_MarkovProcess_V3H_Time_DenseTimeHistory_28830881
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
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conditional kernels for parameterized finite dense-time prefixes

This file disintegrates the jointly parameterized law of a finite dense-time prefix and its next
observation. The resulting conditional kernel is one jointly measurable version. No comparison
with separately chosen fixed-parameter conditional versions is asserted.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

noncomputable section

variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]

/-- The jointly parameterized law of an `n`-prefix and its next enumerated observation. -/
def parameterizedNextObservationJoint
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (e : ℕ ≃ D)
    (iota : D ↪ NNReal) (n : ℕ) :
    Kernel (Theta × alpha) ((Fin n → alpha) × alpha) :=
  Kernel.mapOfMeasurable (P.parameterizedDenseTimePrefixKernel e iota (n + 1))
    (DenseTimeHistory.splitLast n) (DenseTimeHistory.splitLast n).measurable

variable [StandardBorelSpace alpha] [Nonempty alpha]

omit [StandardBorelSpace alpha] [Nonempty alpha] in
/-- The first marginal of the joint law is the preceding parameterized prefix law. -/
theorem p2m_embedded_9ee000bfaf57d55b
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (n : ℕ) :
    (P.parameterizedNextObservationJoint e iota n).fst =
      P.parameterizedDenseTimePrefixKernel e iota n := by
  rw [parameterizedNextObservationJoint, Kernel.mapOfMeasurable_eq_map, Kernel.fst_eq,
    ← Kernel.map_comp_right]
  · change
      (P.parameterizedDenseTimePrefixKernel e iota n.succ).map
          (Prod.fst ∘ DenseTimeHistory.splitLast n) =
        P.parameterizedDenseTimePrefixKernel e iota n
    calc
      (P.parameterizedDenseTimePrefixKernel e iota n.succ).map
          (Prod.fst ∘ DenseTimeHistory.splitLast n) =
          (P.parameterizedDenseTimePrefixKernel e iota n.succ).map
            (FiniteOrderedTimes.restrictPath
              (Fin.castLEOrderEmb (Nat.le_succ n))) := by
        congr 1
        funext path i
        exact DenseTimeHistory.splitLast_fst_apply n path i
      _ = P.parameterizedDenseTimePrefixKernel e iota n :=
        (P.p2m_embedded_7534060ff52e2426
          hP e iota (Nat.le_succ n)).symm
  · exact (DenseTimeHistory.splitLast n).measurable
  · exact measurable_fst

/-- One jointly measurable conditional law of the next observation given the parameter, start,
and preceding prefix. -/
def parameterizedObservationCondKernel
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (n : ℕ) :
    Kernel ((Theta × alpha) × (Fin n → alpha)) alpha := by
  letI : IsMarkovKernel (P.parameterizedNextObservationJoint e iota n) := by
    rw [parameterizedNextObservationJoint, Kernel.mapOfMeasurable_eq_map]
    let : IsMarkovKernel (P.parameterizedDenseTimePrefixKernel e iota (n + 1)) :=
      P.isMarkovKernel_parameterizedDenseTimePrefixKernel hP e iota (n + 1)
    exact Kernel.IsMarkovKernel.map _ (DenseTimeHistory.splitLast n).measurable
  exact (P.parameterizedNextObservationJoint e iota n).condKernel

/-- The jointly parameterized conditional next-observation law is Markov. -/
theorem isMarkovKernel_parameterizedObservationCondKernel
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (n : ℕ) :
    IsMarkovKernel (P.parameterizedObservationCondKernel hP e iota n) := by
  rw [parameterizedObservationCondKernel]
  infer_instance

/-- Disintegration reconstructs the jointly parameterized next-observation law. -/
theorem compProd_parameterizedObservationCondKernel
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (n : ℕ) :
    P.parameterizedDenseTimePrefixKernel e iota n ⊗ₖ
        P.parameterizedObservationCondKernel hP e iota n =
      P.parameterizedNextObservationJoint e iota n := by
  rw [← P.p2m_embedded_9ee000bfaf57d55b hP e iota n]
  rw [parameterizedObservationCondKernel]
  exact Kernel.disintegrate _ _

end
end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess


