-- Prove2me | Definitions.Def_MarkovProcess_V3H_Restart_MixedPastFuture_e5e8ccdc
-- name    : MarkovProcess_V3H_Restart_MixedPastFuture_e5e8ccdc
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T08:01:27.395211+00:00
-- url     : https://prove2.me/theorems/9c577c84-f1be-4c4f-9a75-73e018057b55
-- title:
--   MarkovProcess: MarkovProcess_V3H_Restart_MixedPastFuture_e5e8ccdc
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_PhysicalReindex_4ed652de
import Definitions.Def_MarkovProcess_V3H_DenseTime_Shift_b3e2f7d9
import Definitions.Def_MarkovProcess_V3H_FiniteTime_DenseTimeFiniteShift_11c70184
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelConcatenation_cb54f8d1
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelMixedPullback_8cf93300
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelRestriction_041bf9e5
import Definitions.Def_MarkovProcess_V3H_FiniteTime_Kernel_7ce8d73d
import Definitions.Def_MarkovProcess_V3H_FiniteTime_ProjectiveFamily_1eff0efa
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Path_DenseFiltration_62a9879d
import Definitions.Def_MarkovProcess_V3H_Restart_MixedPastFuture_e5e8ccdc_PartA
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Definitions.Def_MarkovProcess_V3H_Time_FiniteOrderedTimes_717796dd
import Definitions.Def_MarkovProcess_V3H_Trajectory_FiniteMarginals_a8fbfae5
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.LocallyFinite

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Mixed past-future coordinates and the cut factorization

This file merges the following former modules, one section each:

* `MixedPastFutureCoordinates`: Finite coordinates mixing a rational past and shifted future
* `MixedPastFutureCutCoordinates`: Finite mixed coordinates split at their rational terminal time
* `MixedPastFutureCutFactorization`: Factoring finite mixed past/future coordinates at a rational cut
-/

namespace MarkovProcess

section MixedPastFutureCoordinates

open MeasureTheory


noncomputable section

namespace MixedPastFuture



































variable {alpha : Type*} [MeasurableSpace alpha]



end MixedPastFuture

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]











variable [MeasurableSpace alpha] [BorelSpace alpha]



end ContinuousPath

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]



end ContinuousPath
end

end MixedPastFutureCoordinates

section MixedPastFutureCutCoordinates

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace MixedPastFuture

noncomputable section

























































/-- Position of a positive relative-future coordinate in the final ordered block. -/
def positiveFutureOrderIndex (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime))
    (t : positiveFutureFinset S I) : Fin (positiveFutureFinset S I).card :=
  Fin.cast (by
    rw [SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map])
    ((((SubMarkovKernelSemigroup.denseTimePhysicalSet
      (positiveFutureFinset S I)).orderIsoOfFin rfl).symm
        (DenseTime.physicalSetEquiv (positiveFutureFinset S I) t)))

@[simp]
theorem p2m_embedded_d2f1cad2dc2d143e
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (r : pastWithTerminalFinset S I) :
    cutPastOrderedPhysicalTimes S I (pastCutOrderIndex S I r) =
      DenseTime.castOrderEmbedding r := by
  let A := pastPhysicalFinsetWithTerminal S I
  have hcard : A.card = pastPredecessorCard S I + 1 := by
    simp only [A, pastPhysicalFinsetWithTerminal,
      SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map,
      card_pastWithTerminalFinset]
  change A.orderEmbOfFin hcard
    (Fin.cast hcard ((A.orderIsoOfFin rfl).symm
      (DenseTime.physicalSetEquiv (pastWithTerminalFinset S I) r))) = _
  have hx := congrArg Subtype.val ((A.orderIsoOfFin rfl).apply_symm_apply
    (DenseTime.physicalSetEquiv (pastWithTerminalFinset S I) r))
  simpa only [Finset.coe_orderIsoOfFin_apply,
    DenseTime.physicalSetEquiv_apply] using! hx

@[simp]
theorem positiveFutureOrderedPhysicalTimes_positiveFutureOrderIndex
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (t : positiveFutureFinset S I) :
    positiveFutureOrderedPhysicalTimes S I (positiveFutureOrderIndex S I t) =
      DenseTime.castOrderEmbedding t := by
  let F := SubMarkovKernelSemigroup.denseTimePhysicalSet (positiveFutureFinset S I)
  have hcard : F.card = (positiveFutureFinset S I).card := by
    simp only [F, SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map]
  change F.orderEmbOfFin hcard
    (Fin.cast hcard ((F.orderIsoOfFin rfl).symm
      (DenseTime.physicalSetEquiv (positiveFutureFinset S I) t))) = _
  have hx := congrArg Subtype.val ((F.orderIsoOfFin rfl).apply_symm_apply
    (DenseTime.physicalSetEquiv (positiveFutureFinset S I) t))
  simpa only [Finset.coe_orderIsoOfFin_apply,
    DenseTime.physicalSetEquiv_apply] using! hx

/-- Reindex a split ordered path by augmented-past and positive-future dense labels. -/
def orderedSplitToCutCoordinates {alpha : Type*} (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime))
    (z : (Fin (pastPredecessorCard S I + 1) → alpha) ×
      (Fin (positiveFutureFinset S I).card → alpha)) :
    (pastWithTerminalFinset S I → alpha) × (positiveFutureFinset S I → alpha) :=
  (fun r ↦ z.1 (pastCutOrderIndex S I r),
    fun t ↦ z.2 (positiveFutureOrderIndex S I t))

theorem measurable_orderedSplitToCutCoordinates {alpha : Type*} [MeasurableSpace alpha]
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Measurable (orderedSplitToCutCoordinates (alpha := alpha) S I) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro r
    exact (measurable_pi_apply (pastCutOrderIndex S I r)).comp measurable_fst
  · rw [measurable_pi_iff]
    intro t
    exact (measurable_pi_apply (positiveFutureOrderIndex S I t)).comp measurable_snd

/-- A past label as a coordinate of the cut-augmented past set. -/
def pastCutIndex (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (r : I.toLeft) : pastWithTerminalFinset S I :=
  ⟨r.1.1, (mem_pastWithTerminalFinset S I r).mpr
    (Or.inl ⟨r.1.property, Finset.mem_toLeft.mp r.property⟩)⟩

@[simp]
theorem p2m_embedded_f74d5b57e30f1c0e (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (r : I.toLeft) : (pastCutIndex S I r : DenseTime) = r := rfl

/-- A positive future label is a coordinate of the strict future set; future zero is sent to
`none`, meaning that concatenation should read the terminal past coordinate. -/
def futureCutIndex (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (t : I.toRight) : Option (positiveFutureFinset S I) :=
  if ht : t.1 = 0 then none else
    some ⟨t, (mem_positiveFutureFinset S I t).mpr
      ⟨Finset.mem_toRight.mp t.property, bot_lt_iff_ne_bot.mpr ht⟩⟩

@[simp]
theorem p2m_embedded_736fbf2182584b9b (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) (t : I.toRight) :
    futureCutIndex S I t = none ↔ (t : DenseTime) = 0 := by
  simp only [futureCutIndex]
  split <;> simp_all

variable {alpha : Type*}

/-- Select the augmented-past or strict-future coordinate represented by a mixed label. -/
def cutCoordinateIndex (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) (i : I) :
    pastWithTerminalFinset S I ⊕ positiveFutureFinset S I := by
  cases hi : i.1 with
  | inl r =>
      exact Sum.inl ⟨r, (mem_pastWithTerminalFinset S I r).mpr
        (Or.inl ⟨r.property, by simpa only [hi] using i.property⟩)⟩
  | inr t =>
      if ht : t = 0 then
        exact Sum.inl ⟨S, Finset.mem_union_right _ (Finset.mem_singleton_self S)⟩
      else
        exact Sum.inr ⟨t, (mem_positiveFutureFinset S I t).mpr
          ⟨by simpa only [hi] using i.property, bot_lt_iff_ne_bot.mpr ht⟩⟩

/-- Pull coordinates indexed by the augmented past and the strictly positive relative future
back to the original mixed labels. -/
def pullbackCutCoordinates (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (z : (pastWithTerminalFinset S I → alpha) × (positiveFutureFinset S I → alpha)) :
    I → alpha := fun i ↦ Sum.elim z.1 z.2 (cutCoordinateIndex S I i)

variable [MeasurableSpace alpha]

theorem measurable_pullbackCutCoordinates (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Measurable (pullbackCutCoordinates (alpha := alpha) S I) := by
  rw [measurable_pi_iff]
  intro i
  cases h : cutCoordinateIndex S I i with
  | inl r =>
      simpa only [pullbackCutCoordinates, h, Sum.elim_inl] using!
        ((measurable_pi_apply r).comp measurable_fst)
  | inr t =>
      simpa only [pullbackCutCoordinates, h, Sum.elim_inr] using!
        ((measurable_pi_apply t).comp measurable_snd)

/-- Include an original absolute physical coordinate into the cut-augmented set. -/
def includeAbsolutePhysical (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (t : absolutePhysicalFinset S I) : absolutePhysicalFinsetWithTerminal S I :=
  ⟨t, by
    exact (Finset.map_subset_map.mpr Finset.subset_union_left) t.property⟩

/-- Restrict a path on the augmented absolute set to the actually observed absolute set. -/
def restrictAugmentedAbsolute {alpha : Type*} (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime))
    (path : absolutePhysicalFinsetWithTerminal S I → alpha) :
    absolutePhysicalFinset S I → alpha :=
  fun t ↦ path (includeAbsolutePhysical S I t)

/-- Read the augmented absolute path as an augmented past and a strictly positive relative
future. -/
def splitAugmentedAbsolute {alpha : Type*} (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime))
    (path : absolutePhysicalFinsetWithTerminal S I → alpha) :
    (pastWithTerminalFinset S I → alpha) × (positiveFutureFinset S I → alpha) :=
  (fun r ↦ path ⟨DenseTime.castOrderEmbedding r, by
      rw [absolutePhysicalFinsetWithTerminal,
        SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map]
      exact ⟨r, (absoluteFinsetWithTerminal_eq S I).symm.le
        (Finset.mem_union_left _ r.property), rfl⟩⟩,
    fun t ↦ path ⟨DenseTime.castOrderEmbedding (S + t), by
      rw [absolutePhysicalFinsetWithTerminal,
        SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map]
      exact ⟨S + t, (absoluteFinsetWithTerminal_eq S I).symm.le
        (Finset.mem_union_right _ ((DenseTime.mem_addFinset S
          (positiveFutureFinset S I) (S + t)).mpr ⟨t, t.property, rfl⟩)), rfl⟩⟩)

theorem measurable_splitAugmentedAbsolute {alpha : Type*} [MeasurableSpace alpha]
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Measurable (splitAugmentedAbsolute (alpha := alpha) S I) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro r
    exact measurable_pi_apply _
  · rw [measurable_pi_iff]
    intro t
    exact measurable_pi_apply _

/-- Splitting the canonical ordered augmented path gives its augmented-past coordinates and its
strictly positive relative-future coordinates. -/
theorem p2m_embedded_6013cb40e791846c
    {alpha : Type*} (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    orderedSplitToCutCoordinates (alpha := alpha) S I ∘
          SubMarkovKernelSemigroup.splitFinitePath ∘
          FiniteOrderedTimes.restrictPath (cutOrderEmbedding S I) =
      splitAugmentedAbsolute S I ∘
        SubMarkovKernelSemigroup.orderedPathToFiniteSet
          (absolutePhysicalFinsetWithTerminal S I) := by
  funext path
  apply Prod.ext
  · funext r
    change path _ = path _
    apply congrArg path
    apply (SubMarkovKernelSemigroup.finiteSetTimes
      (absolutePhysicalFinsetWithTerminal S I)).injective
    rw [show
      (SubMarkovKernelSemigroup.finiteSetTimes
        (absolutePhysicalFinsetWithTerminal S I))
          (cutOrderEmbedding S I
            (cutIndexOrderIso (pastPredecessorCard S I)
              (positiveFutureFinset S I).card
              (Fin.castAdd (positiveFutureFinset S I).card (pastCutOrderIndex S I r)))) =
        cutOrderedPhysicalTimes S I
          (cutIndexOrderIso (pastPredecessorCard S I)
            (positiveFutureFinset S I).card
            (Fin.castAdd (positiveFutureFinset S I).card (pastCutOrderIndex S I r))) by
      rfl]
    change FiniteOrderedTimes.initialSegment
        (cutOrderedPhysicalTimes S I) (pastCutOrderIndex S I r) =
      (SubMarkovKernelSemigroup.finiteSetTimes
        (absolutePhysicalFinsetWithTerminal S I))
          (((absolutePhysicalFinsetWithTerminal S I).orderIsoOfFin rfl).symm
            ⟨DenseTime.castOrderEmbedding r, _⟩)
    rw [_root_.MarkovProcess.MixedPastFuture.p2m_embedded_b2ac0c93e582fa0b,
      _root_.MarkovProcess.MixedPastFuture.p2m_embedded_d2f1cad2dc2d143e]
    change DenseTime.castOrderEmbedding r =
      (((absolutePhysicalFinsetWithTerminal S I).orderIsoOfFin rfl)
        (((absolutePhysicalFinsetWithTerminal S I).orderIsoOfFin rfl).symm
          ⟨DenseTime.castOrderEmbedding r, _⟩) :
        absolutePhysicalFinsetWithTerminal S I)
    rw [OrderIso.apply_symm_apply]
  · funext t
    change path _ = path _
    apply congrArg path
    apply (SubMarkovKernelSemigroup.finiteSetTimes
      (absolutePhysicalFinsetWithTerminal S I)).injective
    rw [show
      (SubMarkovKernelSemigroup.finiteSetTimes
        (absolutePhysicalFinsetWithTerminal S I))
          (cutOrderEmbedding S I
            (cutIndexOrderIso (pastPredecessorCard S I)
              (positiveFutureFinset S I).card
              (Fin.natAdd (pastPredecessorCard S I + 1)
                (positiveFutureOrderIndex S I t)))) =
        cutOrderedPhysicalTimes S I
          (cutIndexOrderIso (pastPredecessorCard S I)
            (positiveFutureFinset S I).card
            (Fin.natAdd (pastPredecessorCard S I + 1)
              (positiveFutureOrderIndex S I t))) by
      rfl]
    change cutOrderedPhysicalTimes S I
        (cutIndexOrderIso (pastPredecessorCard S I)
          (positiveFutureFinset S I).card
          (Fin.natAdd (pastPredecessorCard S I + 1) (positiveFutureOrderIndex S I t))) =
      (SubMarkovKernelSemigroup.finiteSetTimes
        (absolutePhysicalFinsetWithTerminal S I))
          (((absolutePhysicalFinsetWithTerminal S I).orderIsoOfFin rfl).symm
            ⟨DenseTime.castOrderEmbedding (S + t), _⟩)
    have hcut : cutOrderedPhysicalTimes S I
        (cutIndexOrderIso (pastPredecessorCard S I)
          (positiveFutureFinset S I).card
          (Fin.castAdd (positiveFutureFinset S I).card
            (Fin.last (pastPredecessorCard S I)))) =
        DenseTime.castOrderEmbedding S := by
      change FiniteOrderedTimes.initialSegment
        (cutOrderedPhysicalTimes S I) (Fin.last (pastPredecessorCard S I)) = _
      rw [_root_.MarkovProcess.MixedPastFuture.p2m_embedded_b2ac0c93e582fa0b, _root_.MarkovProcess.MixedPastFuture.p2m_embedded_dd9fcb00834a4bf8]
    have hrelative :
        cutOrderedPhysicalTimes S I
            (cutIndexOrderIso (pastPredecessorCard S I)
              (positiveFutureFinset S I).card
              (Fin.natAdd (pastPredecessorCard S I + 1)
                (positiveFutureOrderIndex S I t))) -
          DenseTime.castOrderEmbedding S = DenseTime.castOrderEmbedding t := by
      rw [← hcut,
        ← FiniteOrderedTimes.relativeFinalSegment_apply,
        _root_.MarkovProcess.MixedPastFuture.p2m_embedded_0d141d3b4a54a0f0,
        positiveFutureOrderedPhysicalTimes_positiveFutureOrderIndex]
    have hle : DenseTime.castOrderEmbedding S ≤
        cutOrderedPhysicalTimes S I
          (cutIndexOrderIso (pastPredecessorCard S I)
            (positiveFutureFinset S I).card
            (Fin.natAdd (pastPredecessorCard S I + 1)
              (positiveFutureOrderIndex S I t))) := by
      rw [← hcut]
      apply (cutOrderedPhysicalTimes S I).monotone
      apply (cutIndexOrderIso
        (pastPredecessorCard S I) (positiveFutureFinset S I).card).monotone
      apply Fin.mk_le_mk.mpr
      change pastPredecessorCard S I ≤
        pastPredecessorCard S I + 1 + (positiveFutureOrderIndex S I t).val
      omega
    have habsolute : cutOrderedPhysicalTimes S I
        (cutIndexOrderIso (pastPredecessorCard S I)
          (positiveFutureFinset S I).card
          (Fin.natAdd (pastPredecessorCard S I + 1)
            (positiveFutureOrderIndex S I t))) =
        DenseTime.castOrderEmbedding (S + t) := by
      calc
        _ = DenseTime.castOrderEmbedding t + DenseTime.castOrderEmbedding S :=
          (tsub_eq_iff_eq_add_of_le hle).mp hrelative
        _ = DenseTime.castOrderEmbedding S + DenseTime.castOrderEmbedding t :=
          add_comm _ _
        _ = DenseTime.castOrderEmbedding (S + t) :=
          (DenseTime.castOrderEmbedding_add S t).symm
    rw [habsolute]
    change DenseTime.castOrderEmbedding (S + t) =
      (((absolutePhysicalFinsetWithTerminal S I).orderIsoOfFin rfl)
        (((absolutePhysicalFinsetWithTerminal S I).orderIsoOfFin rfl).symm
          ⟨DenseTime.castOrderEmbedding (S + t), _⟩) :
        absolutePhysicalFinsetWithTerminal S I)
    rw [OrderIso.apply_symm_apply]

/-- Splitting an augmented absolute path and pulling it back to mixed labels is exactly the
original possibly noninjective absolute-coordinate pullback. -/
theorem p2m_embedded_a2ee832ab4cb5d7e {alpha : Type*}
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (path : absolutePhysicalFinsetWithTerminal S I → alpha) :
    pullbackCutCoordinates S I (splitAugmentedAbsolute S I path) =
      pullbackAbsolutePhysical S I (restrictAugmentedAbsolute S I path) := by
  funext i
  rcases i with ⟨r | t, hi⟩
  · simp only [pullbackCutCoordinates, cutCoordinateIndex, splitAugmentedAbsolute,
      _root_.MarkovProcess.MixedPastFuture.p2m_embedded_795bc4de6d9bacdd, restrictAugmentedAbsolute]
    apply congrArg path
    apply Subtype.ext
    change DenseTime.castOrderEmbedding r = DenseTime.castOrderEmbedding r
    rfl
  · by_cases ht : t = 0
    · subst t
      simp only [pullbackCutCoordinates, cutCoordinateIndex, ↓reduceDIte,
        splitAugmentedAbsolute, _root_.MarkovProcess.MixedPastFuture.p2m_embedded_795bc4de6d9bacdd, restrictAugmentedAbsolute]
      apply congrArg path
      apply Subtype.ext
      change DenseTime.castOrderEmbedding S = DenseTime.castOrderEmbedding (S + 0)
      rw [add_zero]
    · simp only [pullbackCutCoordinates, cutCoordinateIndex, ht, ↓reduceDIte,
        splitAugmentedAbsolute, _root_.MarkovProcess.MixedPastFuture.p2m_embedded_795bc4de6d9bacdd, restrictAugmentedAbsolute]
      apply congrArg path
      apply Subtype.ext
      change DenseTime.castOrderEmbedding (S + t) = DenseTime.castOrderEmbedding (S + t)
      rfl

theorem absolutePhysicalFinset_subset_withTerminal (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    absolutePhysicalFinset S I ⊆ absolutePhysicalFinsetWithTerminal S I := by
  exact Finset.map_subset_map.mpr Finset.subset_union_left



end
end MixedPastFuture

namespace SubMarkovKernelSemigroup
namespace IsConservative

/-- The mixed marginal may be computed from the cut-augmented finite-set law, split into the
augmented past and strict future.  This is the projective reduction which makes omission of `S`
and duplication at future zero harmless before applying ordered concatenation. -/
theorem p2m_embedded_03378c2a64518a14
    {alpha : Type*} [MeasurableSpace alpha]
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    (MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel P
      (MixedPastFuture.absolutePhysicalFinset S I)).map
        (MixedPastFuture.pullbackAbsolutePhysical S I) =
      (MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel P
        (MixedPastFuture.absolutePhysicalFinsetWithTerminal S I)).map
        (MixedPastFuture.pullbackCutCoordinates S I ∘
          MixedPastFuture.splitAugmentedAbsolute S I) := by
  rw [hP.finiteSetKernel_map_restrict₂ P
    (MixedPastFuture.absolutePhysicalFinset_subset_withTerminal S I)]
  let K := MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel P
    (MixedPastFuture.absolutePhysicalFinsetWithTerminal S I)
  change
    (K.map (Finset.restrict₂ (π := fun _ ↦ alpha)
      (MixedPastFuture.absolutePhysicalFinset_subset_withTerminal S I))).map
        (MixedPastFuture.pullbackAbsolutePhysical S I) = _
  calc
    (K.map (Finset.restrict₂ (π := fun _ ↦ alpha)
        (MixedPastFuture.absolutePhysicalFinset_subset_withTerminal S I))).map
          (MixedPastFuture.pullbackAbsolutePhysical S I) =
        K.map (MixedPastFuture.pullbackAbsolutePhysical S I ∘
          Finset.restrict₂ (π := fun _ ↦ alpha)
            (MixedPastFuture.absolutePhysicalFinset_subset_withTerminal S I)) := by
      exact (ProbabilityTheory.Kernel.map_comp_right K
        (Finset.measurable_restrict₂ (X := fun _ ↦ alpha)
          (MixedPastFuture.absolutePhysicalFinset_subset_withTerminal S I))
        (MixedPastFuture.measurable_pullbackAbsolutePhysical S I)).symm
    _ = K.map (MixedPastFuture.pullbackCutCoordinates S I ∘
          MixedPastFuture.splitAugmentedAbsolute S I) := by
      congr 1
      funext path
      exact (_root_.MarkovProcess.MixedPastFuture.p2m_embedded_a2ee832ab4cb5d7e S I path).symm



end IsConservative
end SubMarkovKernelSemigroup

end MixedPastFutureCutCoordinates

section MixedPastFutureCutFactorization

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace SubMarkovKernelSemigroup
namespace IsConservative

/-- A mixed finite marginal factors into its cut-augmented past law and the strict relative-future
law started from the terminal past coordinate. -/
theorem p2m_embedded_288b67af558fbc9a
    {alpha : Type*} [MeasurableSpace alpha]
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    (finiteSetKernel P (MixedPastFuture.absolutePhysicalFinset S I)).map
        (MixedPastFuture.pullbackAbsolutePhysical S I) =
      ((finiteTimeKernel P (MixedPastFuture.cutPastOrderedPhysicalTimes S I)) ⊗ₖ
        (finiteTimeKernel P
          (MixedPastFuture.positiveFutureOrderedPhysicalTimes S I)).comap
            (splitPastTerminal (alpha := alpha)
              (m := MixedPastFuture.pastPredecessorCard S I))
            measurable_splitPastTerminal).map
        (MixedPastFuture.pullbackCutCoordinates S I ∘
          MixedPastFuture.orderedSplitToCutCoordinates S I) := by
  rw [hP.p2m_embedded_03378c2a64518a14 P S I,
    finiteSetKernel_eq_map]
  let G := MixedPastFuture.pullbackCutCoordinates (alpha := alpha) S I ∘
    MixedPastFuture.orderedSplitToCutCoordinates S I
  have hG : Measurable G :=
    (MixedPastFuture.measurable_pullbackCutCoordinates S I).comp
      (MixedPastFuture.measurable_orderedSplitToCutCoordinates S I)
  have hsplit : Measurable
      (splitFinitePath (alpha := alpha)
        (m := MixedPastFuture.pastPredecessorCard S I)
        (n := (MixedPastFuture.positiveFutureFinset S I).card)) :=
    measurable_splitFinitePath
  have hreindex : Measurable
      (FiniteOrderedTimes.restrictPath (MixedPastFuture.cutOrderEmbedding S I) :
        (Fin (MixedPastFuture.absolutePhysicalFinsetWithTerminal S I).card → alpha) →
          Fin ((MixedPastFuture.positiveFutureFinset S I).card +
            (MixedPastFuture.pastPredecessorCard S I + 1)) → alpha) :=
    FiniteOrderedTimes.measurable_restrictPath _
  let K := finiteTimeKernel P
    (finiteSetTimes (MixedPastFuture.absolutePhysicalFinsetWithTerminal S I))
  calc
    (K.map (orderedPathToFiniteSet
        (MixedPastFuture.absolutePhysicalFinsetWithTerminal S I))).map
          (MixedPastFuture.pullbackCutCoordinates S I ∘
            MixedPastFuture.splitAugmentedAbsolute S I) =
        K.map ((MixedPastFuture.pullbackCutCoordinates S I ∘
            MixedPastFuture.splitAugmentedAbsolute S I) ∘
          orderedPathToFiniteSet
            (MixedPastFuture.absolutePhysicalFinsetWithTerminal S I)) := by
      exact (Kernel.map_comp_right K
        (measurable_orderedPathToFiniteSet
          (MixedPastFuture.absolutePhysicalFinsetWithTerminal S I))
        ((MixedPastFuture.measurable_pullbackCutCoordinates S I).comp
          (MixedPastFuture.measurable_splitAugmentedAbsolute S I))).symm
    _ = K.map ((G ∘ splitFinitePath) ∘
          FiniteOrderedTimes.restrictPath (MixedPastFuture.cutOrderEmbedding S I)) := by
      congr 1
      funext path
      exact congrArg (MixedPastFuture.pullbackCutCoordinates S I)
        (congrFun
          (_root_.MarkovProcess.MixedPastFuture.p2m_embedded_6013cb40e791846c
            (alpha := alpha) S I) path).symm
    _ = (K.map (FiniteOrderedTimes.restrictPath
          (MixedPastFuture.cutOrderEmbedding S I))).map
          (G ∘ splitFinitePath) := by
      exact Kernel.map_comp_right K hreindex (hG.comp hsplit)
    _ = (finiteTimeKernel P (MixedPastFuture.cutOrderedPhysicalTimes S I)).map
          (G ∘ splitFinitePath) := by
      rw [hP.p2m_embedded_df60a2ab25853e30 P
        (finiteSetTimes (MixedPastFuture.absolutePhysicalFinsetWithTerminal S I))
        (MixedPastFuture.cutOrderEmbedding S I)]
      rfl
    _ = ((finiteTimeKernel P (MixedPastFuture.cutOrderedPhysicalTimes S I)).map
          splitFinitePath).map G := by
      exact Kernel.map_comp_right _ hsplit hG
    _ = ((finiteTimeKernel P
            (FiniteOrderedTimes.initialSegment
              (MixedPastFuture.cutOrderedPhysicalTimes S I))) ⊗ₖ
          (finiteTimeKernel P
            (FiniteOrderedTimes.relativeFinalSegment
              (MixedPastFuture.cutOrderedPhysicalTimes S I))).comap
              (splitPastTerminal (alpha := alpha)
                (m := MixedPastFuture.pastPredecessorCard S I))
              measurable_splitPastTerminal).map G := by
      rw [hP.p2m_embedded_697015a986c844a8 P
        (MixedPastFuture.pastPredecessorCard S I)
        (MixedPastFuture.positiveFutureFinset S I).card
        (MixedPastFuture.cutOrderedPhysicalTimes S I)]
    _ = _ := by
      rw [_root_.MarkovProcess.MixedPastFuture.p2m_embedded_b2ac0c93e582fa0b,
        _root_.MarkovProcess.MixedPastFuture.p2m_embedded_0d141d3b4a54a0f0]

end IsConservative
end SubMarkovKernelSemigroup

end MixedPastFutureCutFactorization

end MarkovProcess


