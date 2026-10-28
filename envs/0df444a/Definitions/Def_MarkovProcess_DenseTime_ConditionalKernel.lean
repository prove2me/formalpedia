-- Prove2me | Definitions.Def_MarkovProcess_DenseTime_ConditionalKernel
-- name    : MarkovProcess_DenseTime_ConditionalKernel
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T13:01:41.559273+00:00
-- url     : https://prove2.me/theorems/3dda458f-426f-47f3-b683-1be7cefcc3d3
-- title:
--   MarkovProcess definitions: DenseTime.ConditionalKernel
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.DenseTime.ConditionalKernel`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/DenseTime/ConditionalKernel.lean#L1-L139

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_DenseTime_PrefixKernel
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_FiniteTime_ProjectiveFamily
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
import Definitions.Def_MarkovProcess_Time_DenseTimeHistory
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
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

/-!
# Conditional kernels for finite dense-time histories

This file augments finite prefix laws by their starting point and disintegrates the joint law of
a prefix and its next observation. It makes no infinite-process or path-regularity claim.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

noncomputable section

variable {D α : Type*} [MeasurableSpace α]

/-- The law of a finite history, including the deterministic starting point. -/
def augmentedPrefixKernel (P : SubMarkovKernelSemigroup α) (e : ℕ ≃ D)
    (ι : D ↪ NNReal) (n : ℕ) : Kernel α (DenseTimeHistory α n) :=
  Kernel.mapOfMeasurable
    (Kernel.id ×ₖ denseTimePrefixKernel P e ι n)
    (DenseTimeHistory.historyEquiv n).symm
    (DenseTimeHistory.historyEquiv n).symm.measurable



/-- The joint law of an `n`-prefix and the next enumerated observation. -/
def nextObservationJoint (P : SubMarkovKernelSemigroup α) (e : ℕ ≃ D)
    (ι : D ↪ NNReal) (n : ℕ) : Kernel α ((Fin n → α) × α) :=
  Kernel.mapOfMeasurable (denseTimePrefixKernel P e ι (n + 1))
    (DenseTimeHistory.splitLast n) (DenseTimeHistory.splitLast n).measurable

namespace IsConservative

variable [StandardBorelSpace α] [Nonempty α]





/-- A regular conditional law of the next observation given the start and preceding prefix. -/
def observationCondKernel (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) : Kernel (α × (Fin n → α)) α := by
  letI : IsMarkovKernel (nextObservationJoint P e ι n) := by
    rw [nextObservationJoint, Kernel.mapOfMeasurable_eq_map]
    let : IsMarkovKernel (denseTimePrefixKernel P e ι (n + 1)) :=
      hP.isMarkovKernel_denseTimePrefixKernel P e ι (n + 1)
    exact Kernel.IsMarkovKernel.map _ (DenseTimeHistory.splitLast n).measurable
  exact (nextObservationJoint P e ι n).condKernel

/-- The conditional next-observation law is Markov. -/
theorem isMarkovKernel_observationCondKernel (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    IsMarkovKernel (observationCondKernel P hP e ι n) := by
  rw [observationCondKernel]
  infer_instance



/-- The conditional next-observation law, viewed as a kernel on finite histories. -/
def denseStep (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) : Kernel (DenseTimeHistory α n) α :=
  Kernel.comap (observationCondKernel P hP e ι n)
    (DenseTimeHistory.historyEquiv n) (DenseTimeHistory.historyEquiv n).measurable

/-- The finite-history next-observation kernel is Markov. -/
theorem isMarkovKernel_denseStep (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    IsMarkovKernel (denseStep P hP e ι n) := by
  rw [denseStep]
  let : IsMarkovKernel (observationCondKernel P hP e ι n) :=
    isMarkovKernel_observationCondKernel P hP e ι n
  infer_instance

end IsConservative
end
end SubMarkovKernelSemigroup
end MarkovProcess


