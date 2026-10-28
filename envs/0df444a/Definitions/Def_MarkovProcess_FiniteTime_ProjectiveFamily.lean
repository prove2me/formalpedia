-- Prove2me | Definitions.Def_MarkovProcess_FiniteTime_ProjectiveFamily
-- name    : MarkovProcess_FiniteTime_ProjectiveFamily
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T12:50:58.619751+00:00
-- url     : https://prove2.me/theorems/24456d2c-33a6-49fb-b715-40c539c120f9
-- title:
--   MarkovProcess definitions: FiniteTime.ProjectiveFamily
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.FiniteTime.ProjectiveFamily`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/ProjectiveFamily.lean#L1-L128

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
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

/-!
# Finite-set finite-time laws

This file reindexes the ordered finite-time kernels by finite sets of times and proves their
Mathlib-native projectivity. It does not assert or construct a projective-limit measure.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

variable {α : Type*} [MeasurableSpace α]

/-- The increasing enumeration of a finite set of nonnegative times. -/
noncomputable def finiteSetTimes (I : Finset NNReal) : FiniteOrderedTimes I.card :=
  I.orderEmbOfFin rfl

/-- Reindex an ordered coordinate path by its finite set of times. -/
noncomputable def orderedPathToFiniteSet (I : Finset NNReal) (path : Fin I.card → α) : I → α :=
  fun t ↦ path ((I.orderIsoOfFin rfl).symm t)

/-- Reindexing an ordered coordinate path by its finite set of times is measurable. -/
theorem measurable_orderedPathToFiniteSet (I : Finset NNReal) :
    Measurable (orderedPathToFiniteSet (α := α) I) :=
  measurable_pi_iff.mpr fun t ↦ measurable_pi_apply ((I.orderIsoOfFin rfl).symm t)

/-- The finite-time kernel indexed by a finite set of times. -/
noncomputable def finiteSetKernel (P : SubMarkovKernelSemigroup α) (I : Finset NNReal) :
    Kernel α (I → α) :=
  Kernel.mapOfMeasurable (finiteTimeKernel P (finiteSetTimes I))
    (orderedPathToFiniteSet I) (measurable_orderedPathToFiniteSet I)

/-- The finite-set kernel agrees with the ordinary kernel map. -/
theorem finiteSetKernel_eq_map (P : SubMarkovKernelSemigroup α) (I : Finset NNReal) :
    finiteSetKernel P I =
      (finiteTimeKernel P (finiteSetTimes I)).map (orderedPathToFiniteSet I) :=
  Kernel.mapOfMeasurable_eq_map _ (measurable_orderedPathToFiniteSet I)



private noncomputable def inclusionOrderEmb {I J : Finset NNReal} (hJI : J ⊆ I) :
    Fin J.card ↪o Fin I.card :=
  (J.orderIsoOfFin rfl).toOrderEmbedding |>.trans
    (OrderEmbedding.ofStrictMono
      (fun t : J ↦ (⟨t, hJI t.property⟩ : I)) (fun _ _ h ↦ h)) |>.trans
    (I.orderIsoOfFin rfl).symm.toOrderEmbedding





namespace IsConservative

/-- Under conservativity, every finite-set kernel is a Markov kernel. -/
theorem isMarkovKernel_finiteSetKernel (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (I : Finset NNReal) : IsMarkovKernel (finiteSetKernel P I) := by
  rw [finiteSetKernel_eq_map]
  let : IsMarkovKernel (finiteTimeKernel P (finiteSetTimes I)) :=
    hP.isMarkovKernel_finiteTimeKernel P (finiteSetTimes I)
  exact Kernel.IsMarkovKernel.map _ (measurable_orderedPathToFiniteSet I)







end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess


