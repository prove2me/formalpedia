-- Prove2me | Definitions.Def_MarkovProcess_V3H_Trajectory_FiniteMarginals_a8fbfae5
-- name    : MarkovProcess_V3H_Trajectory_FiniteMarginals_a8fbfae5
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:55:24.406038+00:00
-- url     : https://prove2.me/theorems/06f5ce3c-bac8-481f-a523-ead4e0413ed2
-- title:
--   MarkovProcess: MarkovProcess_V3H_Trajectory_FiniteMarginals_a8fbfae5
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_DenseTime_PrefixKernel_a192bbea
import Definitions.Def_MarkovProcess_V3H_DenseTime_Trajectory_b0f7f66f
import Definitions.Def_MarkovProcess_V3H_FiniteTime_ProjectiveFamily_1eff0efa
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Definitions.Def_MarkovProcess_V3H_Trajectory_Basic_34bd0835
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.SpecificLimits.Basic
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
# Finite rational-time marginals of continuous-path trajectories

This file transports the finite-dimensional laws of the canonical dense-time trajectory to
arbitrary finite sets of nonnegative rational times.  The target coordinates are indexed by the
corresponding finite set of physical `NNReal` times, exactly as in `finiteSetKernel`.

No assertion is made at irrational times or about a Markov, strong Markov, or Hunt property of
the continuous-path law.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

noncomputable section

/-- The finite set of physical nonnegative-real times represented by rational times in `I`. -/
def denseTimePhysicalSet (I : Finset DenseTime) : Finset NNReal :=
  I.map DenseTime.castOrderEmbedding.toEmbedding

private theorem exists_denseTimePhysicalSet_subset_prefix
    (e : ℕ ≃ DenseTime) (I : Finset DenseTime) :
    ∃ n, denseTimePhysicalSet I ⊆
      denseTimePhysicalPrefix e DenseTime.castOrderEmbedding.toEmbedding n := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      intro t ht
      simp only [denseTimePhysicalSet, Finset.map_empty, Finset.notMem_empty] at ht
  | @insert a I ha ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨max n (e.symm a + 1), ?_⟩
      intro t ht
      rw [denseTimePhysicalSet, Finset.mem_map] at ht
      obtain ⟨d, hd, rfl⟩ := ht
      rw [denseTimePhysicalPrefix, Finset.mem_map]
      refine ⟨d, ?_, rfl⟩
      rw [CountableEnumeration.mem_prefix_iff]
      rw [Finset.mem_insert] at hd
      rcases hd with rfl | hd
      · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
      · have hmem : DenseTime.castOrderEmbedding d ∈ denseTimePhysicalSet I := by
          rw [denseTimePhysicalSet, Finset.mem_map]
          exact ⟨d, hd, rfl⟩
        have hprefix := hn hmem
        rw [denseTimePhysicalPrefix, Finset.mem_map] at hprefix
        obtain ⟨d', hd', heq⟩ := hprefix
        have hdd' : d = d' := DenseTime.castOrderEmbedding.injective heq.symm
        subst d'
        rw [CountableEnumeration.mem_prefix_iff] at hd'
        exact Nat.lt_of_lt_of_le hd' (le_max_left _ _)

private noncomputable def finEquivDenseTimePhysicalPrefix
    (e : ℕ ≃ DenseTime) (n : ℕ) :
    Fin n ≃ denseTimePhysicalPrefix e DenseTime.castOrderEmbedding.toEmbedding n :=
  Equiv.ofBijective
    (fun i ↦
      ⟨DenseTime.castOrderEmbedding (e i), by
        rw [denseTimePhysicalPrefix, Finset.mem_map]
        exact ⟨e i, by
          rw [CountableEnumeration.mem_prefix_iff, e.symm_apply_apply]
          exact i.isLt, rfl⟩⟩)
    ⟨by
      intro i j hij
      apply Fin.ext
      apply e.injective
      apply DenseTime.castOrderEmbedding.injective
      exact congrArg Subtype.val hij,
    by
      intro t
      have ht := t.property
      change t.val ∈ (CountableEnumeration.prefix e n).map
        DenseTime.castOrderEmbedding.toEmbedding at ht
      rw [Finset.mem_map] at ht
      obtain ⟨d, hd, hdt⟩ := ht
      let i : Fin n := ⟨e.symm d, by
        rw [CountableEnumeration.mem_prefix_iff] at hd
        exact hd⟩
      refine ⟨i, Subtype.ext ?_⟩
      change DenseTime.castOrderEmbedding (e i) = t
      rw [show e i = d by exact e.apply_symm_apply d]
      exact hdt⟩

variable {α : Type*}

private def physicalPrefixPathOfFinPath
    (e : ℕ ≃ DenseTime) (n : ℕ) (path : Fin n → α) :
    denseTimePhysicalPrefix e DenseTime.castOrderEmbedding.toEmbedding n → α :=
  fun t ↦ path ((finEquivDenseTimePhysicalPrefix e n).symm t)

private theorem measurable_physicalPrefixPathOfFinPath
    [MeasurableSpace α] (e : ℕ ≃ DenseTime) (n : ℕ) :
    Measurable (physicalPrefixPathOfFinPath (α := α) e n) :=
  measurable_pi_iff.mpr fun t ↦
    measurable_pi_apply ((finEquivDenseTimePhysicalPrefix e n).symm t)

namespace IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

private theorem continuousPathTrajectory_map_physicalPrefix
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (n : ℕ) :
    (continuousPathTrajectory P hP default).map
        (fun path (t : denseTimePhysicalPrefix DenseTime.enumeration
          DenseTime.castOrderEmbedding.toEmbedding n) ↦ path t) =
      finiteSetKernel P (denseTimePhysicalPrefix DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding n) := by
  let equiv := finEquivDenseTimePhysicalPrefix DenseTime.enumeration n
  have hleft :
      physicalPrefixPathOfFinPath (α := alpha) DenseTime.enumeration n ∘
          (denseTimeTrajectoryPrefix DenseTime.enumeration n ∘
            ContinuousPath.denseRestriction) =
        fun path (t : denseTimePhysicalPrefix DenseTime.enumeration
          DenseTime.castOrderEmbedding.toEmbedding n) ↦ path t := by
    funext path t
    change path (DenseTime.castOrderEmbedding
      (DenseTime.enumeration (equiv.symm t))) = path t
    have heq := equiv.apply_symm_apply t
    exact congrArg path (congrArg Subtype.val heq)
  have hright :
      physicalPrefixPathOfFinPath (α := alpha) DenseTime.enumeration n ∘
          denseTimePrefixReindex DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding n = id := by
    funext path t
    change path (equiv (equiv.symm t)) = path t
    rw [equiv.apply_symm_apply]
  rw [← hleft, Kernel.map_comp_right]
  · rw [_root_.MarkovProcess.SubMarkovKernelSemigroup.IsConservative.p2m_embedded_364455a2d9664b7b P hP default hK n,
      denseTimePrefixKernel_eq_map, ← Kernel.map_comp_right]
    · rw [hright, Kernel.map_id]
    · exact measurable_denseTimePrefixReindex DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding n
    · exact measurable_physicalPrefixPathOfFinPath DenseTime.enumeration n
  · exact (measurable_denseTimeTrajectoryPrefix DenseTime.enumeration n).comp
      ContinuousPath.measurable_denseRestriction
  · exact measurable_physicalPrefixPathOfFinPath DenseTime.enumeration n

/-- Every finite rational-time marginal of the continuous-path trajectory is the existing
finite-set kernel at the corresponding physical times. -/
theorem p2m_embedded_b819d8df72e216cf
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (I : Finset DenseTime) :
    (continuousPathTrajectory P hP default).map
        (fun path (t : denseTimePhysicalSet I) ↦ path t) =
      finiteSetKernel P (denseTimePhysicalSet I) := by
  obtain ⟨n, hsubset⟩ :=
    exists_denseTimePhysicalSet_subset_prefix DenseTime.enumeration I
  have hfun :
      (fun path : ContinuousPath alpha ↦
        fun t : denseTimePhysicalSet I ↦ path t) =
      Finset.restrict₂ (π := fun _ ↦ alpha) hsubset ∘
        (fun path : ContinuousPath alpha ↦
          fun t : denseTimePhysicalPrefix DenseTime.enumeration
          DenseTime.castOrderEmbedding.toEmbedding n ↦ path t) := by
    rfl
  rw [hfun, Kernel.map_comp_right]
  · rw [continuousPathTrajectory_map_physicalPrefix P hP default hK n]
    exact (hP.finiteSetKernel_map_restrict₂ P hsubset).symm
  · apply measurable_pi_iff.mpr
    intro t
    rw [BorelSpace.measurable_eq (α := alpha)]
    exact (ContinuousPath.continuous_eval (alpha := alpha) (t : NNReal)).borel_measurable
  · exact Finset.measurable_restrict₂ (X := fun _ ↦ alpha) hsubset

end IsConservative
end
end SubMarkovKernelSemigroup
end MarkovProcess


