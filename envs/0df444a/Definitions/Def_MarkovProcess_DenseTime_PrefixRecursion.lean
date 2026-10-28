-- Prove2me | Definitions.Def_MarkovProcess_DenseTime_PrefixRecursion
-- name    : MarkovProcess_DenseTime_PrefixRecursion
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T13:05:59.017978+00:00
-- url     : https://prove2.me/theorems/1640ccf4-9af9-466f-a0f6-6992537ab858
-- title:
--   MarkovProcess definitions: DenseTime.PrefixRecursion
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.DenseTime.PrefixRecursion`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/DenseTime/PrefixRecursion.lean#L1-L187

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_DenseTime_ConditionalKernel
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
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# One-step recursion for finite dense-time histories

This file identifies the result of adjoining one conditionally sampled observation to an
augmented finite history. It makes no infinite-process or path-regularity claim.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.Kernel





end ProbabilityTheory.Kernel

namespace MarkovProcess
namespace DenseTimeHistory

variable {α : Type*} [MeasurableSpace α]

/-- Adjoin one observation at the end of a finite dense-time history. -/
def append (n : ℕ) : DenseTimeHistory α n × α → DenseTimeHistory α (n + 1) :=
  fun hx ↦ (historyEquiv (n + 1)).symm
    ((historyEquiv n hx.1).1, (splitLast n).symm ((historyEquiv n hx.1).2, hx.2))









end DenseTimeHistory

namespace SubMarkovKernelSemigroup

noncomputable section

variable {D α : Type*} [MeasurableSpace α]

namespace IsConservative

variable [StandardBorelSpace α] [Nonempty α]



end IsConservative
end
end SubMarkovKernelSemigroup

end MarkovProcess


