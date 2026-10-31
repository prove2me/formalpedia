-- Prove2me | Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelShift_14b03019
-- name    : MarkovProcess_V3H_FiniteTime_FiniteSetKernelShift_14b03019
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:38:18.810732+00:00
-- url     : https://prove2.me/theorems/bebda856-4b89-4968-866b-2d7feed35c5d
-- title:
--   MarkovProcess: MarkovProcess_V3H_FiniteTime_FiniteSetKernelShift_14b03019
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_FiniteTime_DenseTimeFiniteShift_11c70184
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelShift_4030eb49
import Definitions.Def_MarkovProcess_V3H_FiniteTime_ProjectiveFamily_1eff0efa
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Translation of finite-set kernels

This file translates finite sets of nonnegative observation times, reindexes paths on the
translated set back to the original coordinates, and proves the corresponding translation law
for conservative transition-kernel semigroups.  It is finite-dimensional kernel infrastructure;
it does not assert a path-space Markov property.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

noncomputable section

/-- The image of a finite set of nonnegative times under translation by `s`. -/
def finiteSetTranslate (s : NNReal) (I : Finset NNReal) : Finset NNReal :=
  I.map (addLeftEmbedding s)

@[simp]
theorem mem_finiteSetTranslate (s : NNReal) (I : Finset NNReal) (t : NNReal) :
    t ∈ finiteSetTranslate s I ↔ ∃ r ∈ I, s + r = t := by
  rw [finiteSetTranslate, Finset.mem_map]
  rfl

/-- Translation identifies the original finite time set with its translated image. -/
def finiteSetTranslateEquiv (s : NNReal) (I : Finset NNReal) : I ≃ finiteSetTranslate s I :=
  Equiv.ofBijective
    (fun t ↦ ⟨s + t, (mem_finiteSetTranslate s I (s + t)).mpr ⟨t, t.property, rfl⟩⟩)
    ⟨by
      intro t u h
      apply Subtype.ext
      exact add_left_cancel (congrArg Subtype.val h),
    by
      intro t
      obtain ⟨r, hrI, hrt⟩ := (mem_finiteSetTranslate s I t).mp t.property
      exact ⟨⟨r, hrI⟩, Subtype.ext hrt⟩⟩



/-- Reindex a path on translated times back to the original finite set. -/
def pullbackFiniteSetTranslate {alpha : Type*} (s : NNReal) (I : Finset NNReal)
    (path : finiteSetTranslate s I → alpha) : I → alpha :=
  fun t ↦ path (finiteSetTranslateEquiv s I t)

@[simp]
theorem p2m_embedded_4122f7a5b7ca3ce9 {alpha : Type*} (s : NNReal) (I : Finset NNReal)
    (path : finiteSetTranslate s I → alpha) (t : I) :
    pullbackFiniteSetTranslate s I path t = path (finiteSetTranslateEquiv s I t) :=
  rfl



private def finiteSetTranslateFinOrderIso (s : NNReal) (I : Finset NNReal) :
    Fin I.card ≃o Fin (finiteSetTranslate s I).card :=
  Fin.castOrderIso (by simp only [finiteSetTranslate, Finset.card_map])





namespace IsConservative

variable {alpha : Type*} [MeasurableSpace alpha]



end IsConservative

end
end SubMarkovKernelSemigroup

namespace DenseTime



end DenseTime
end MarkovProcess


