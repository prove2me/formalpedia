-- Prove2me | Definitions.Def_MarkovProcess_DenseTime_PrefixKernel
-- name    : MarkovProcess_DenseTime_PrefixKernel
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T12:56:30.005994+00:00
-- url     : https://prove2.me/theorems/ee8637c4-3325-4e2f-927e-acd36ed12102
-- title:
--   MarkovProcess definitions: DenseTime.PrefixKernel
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.DenseTime.PrefixKernel`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/DenseTime/PrefixKernel.lean#L1-L119

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_FiniteTime_ProjectiveFamily
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
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

/-!
# Kernels on finite prefixes of a countable time enumeration

This file constructs the finite-dimensional kernel on the first `n` points of an arbitrary
enumeration, with coordinates retained in enumeration order. The enumeration need not respect
the order of physical time.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

noncomputable section

variable {D α : Type*} [MeasurableSpace α]

/-- The physical times occurring in the first `n` positions of an enumeration. -/
def denseTimePhysicalPrefix (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) : Finset NNReal :=
  (CountableEnumeration.prefix e n).map ι



private theorem denseTime_mem_physicalPrefix (e : ℕ ≃ D) (ι : D ↪ NNReal)
    (n : ℕ) (i : Fin n) : ι (e i) ∈ denseTimePhysicalPrefix e ι n := by
  rw [denseTimePhysicalPrefix, Finset.mem_map]
  exact ⟨e i, by
    rw [CountableEnumeration.mem_prefix_iff, e.symm_apply_apply]
    exact i.isLt, rfl⟩

/-- Reindex a path on the physical prefix by its enumeration positions. -/
def denseTimePrefixReindex (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ)
    (path : denseTimePhysicalPrefix e ι n → α) : Fin n → α :=
  fun i ↦ path ⟨ι (e i), denseTime_mem_physicalPrefix e ι n i⟩

/-- Reindexing a physical-prefix path by enumeration positions is measurable. -/
theorem measurable_denseTimePrefixReindex (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    Measurable (denseTimePrefixReindex (α := α) e ι n) :=
  measurable_pi_iff.mpr fun i ↦ measurable_pi_apply
    (⟨ι (e i), denseTime_mem_physicalPrefix e ι n i⟩ : denseTimePhysicalPrefix e ι n)

/-- The finite-dimensional kernel on the first `n` enumerated physical times, with coordinates
in enumeration order. -/
def denseTimePrefixKernel (P : SubMarkovKernelSemigroup α) (e : ℕ ≃ D)
    (ι : D ↪ NNReal) (n : ℕ) : Kernel α (Fin n → α) :=
  Kernel.mapOfMeasurable (finiteSetKernel P (denseTimePhysicalPrefix e ι n))
    (denseTimePrefixReindex e ι n) (measurable_denseTimePrefixReindex e ι n)

/-- The enumeration-prefix kernel agrees with the ordinary kernel map. -/
theorem denseTimePrefixKernel_eq_map (P : SubMarkovKernelSemigroup α) (e : ℕ ≃ D)
    (ι : D ↪ NNReal) (n : ℕ) :
    denseTimePrefixKernel P e ι n =
      (finiteSetKernel P (denseTimePhysicalPrefix e ι n)).map
        (denseTimePrefixReindex e ι n) :=
  Kernel.mapOfMeasurable_eq_map _ (measurable_denseTimePrefixReindex e ι n)



namespace IsConservative

/-- Under conservativity, each enumeration-prefix kernel is a Markov kernel. -/
theorem isMarkovKernel_denseTimePrefixKernel (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    IsMarkovKernel (denseTimePrefixKernel P e ι n) := by
  rw [denseTimePrefixKernel_eq_map]
  let : IsMarkovKernel (finiteSetKernel P (denseTimePhysicalPrefix e ι n)) :=
    hP.isMarkovKernel_finiteSetKernel P _
  exact Kernel.IsMarkovKernel.map _ (measurable_denseTimePrefixReindex e ι n)





end IsConservative
end
end SubMarkovKernelSemigroup
end MarkovProcess


