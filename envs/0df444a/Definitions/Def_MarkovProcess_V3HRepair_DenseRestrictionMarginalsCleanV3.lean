-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_DenseRestrictionMarginalsCleanV3
-- name    : MarkovProcess_V3HRepair_DenseRestrictionMarginalsCleanV3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T10:03:18.980773+00:00
-- url     : https://prove2.me/theorems/3ef81b32-6d6d-4ca1-a0a2-7e1025a75b7e
-- title:
--   Verified MarkovProcess source repair: DenseRestrictionMarginalsCleanV3
-- statement:
--   Enumeration-prefix and arbitrary finite rational-time marginals of continuous-path trajectories agree with their corresponding finite-time Markov kernels.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream commit 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.DenseRestrictionMarginalsCleanV3 SHA-256 76593c652bf8a66592e654c8192ebac8444a0ad5621b97cf2036cc977e836900. Only repaired import paths were translated to the published Definitions.Def_MarkovProcess_V3HRepair_* module names.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3HRepair_FellerMeasureSupportCleanV2


open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
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
/-- Every finite enumeration-prefix marginal of the continuous-path transport is the already
constructed dense-time prefix law. -/
theorem continuousPathTrajectory_map_prefix
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (n : ℕ) :
    (continuousPathTrajectory P hP default).map
        (denseTimeTrajectoryPrefix DenseTime.enumeration n ∘
          ContinuousPath.denseRestriction) =
      denseTimePrefixKernel P DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding n := by
  let kappa := denseTimeTrajectory P hP DenseTime.enumeration
    DenseTime.castOrderEmbedding.toEmbedding
  have hback :
      (continuousPathTrajectory P hP default).map ContinuousPath.denseRestriction = kappa := by
    exact Kernel.map_denseRestriction_toContinuousPathKernel_of_isKolmogorovCoordinate
      kappa default hK
  rw [Kernel.map_comp_right]
  · rw [hback]
    exact denseTimeTrajectory_map_prefix P hP DenseTime.enumeration
      DenseTime.castOrderEmbedding.toEmbedding n
  · exact ContinuousPath.measurable_denseRestriction
  · exact measurable_denseTimeTrajectoryPrefix DenseTime.enumeration n

end IsConservative
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
  · rw [continuousPathTrajectory_map_prefix P hP default hK n,
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
theorem continuousPathTrajectory_map_finiteDenseTimeSet
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
end MarkovProcess.SubMarkovKernelSemigroup
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

/-- Every finite restriction of the dense-time pushforward of the continuous trajectory has the
finite-set transition law at the corresponding physical times, reindexed by rational labels. -/
theorem continuousPathTrajectory_map_denseRestriction_map_restrict
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (I : Finset DenseTime) :
    ((continuousPathTrajectory P hP default).map
        ContinuousPath.denseRestriction).map I.restrict =
      (finiteSetKernel P (denseTimePhysicalSet I)).map
        (DenseTimePath.pullbackPhysicalSet I) := by
  let evaluatePhysical : ContinuousPath alpha → denseTimePhysicalSet I → alpha :=
    fun path t ↦ path t
  have hEvaluate : Measurable evaluatePhysical := by
    rw [measurable_pi_iff]
    intro t
    rw [BorelSpace.measurable_eq (α := alpha)]
    exact (ContinuousPath.continuous_eval (alpha := alpha) (t : NNReal)).borel_measurable
  have hfun :
      I.restrict ∘ ContinuousPath.denseRestriction =
        DenseTimePath.pullbackPhysicalSet I ∘ evaluatePhysical := by
    funext path
    exact (DenseTimePath.pullbackPhysicalSet_evaluation I path).symm
  rw [← Kernel.map_comp_right]
  · rw [hfun, Kernel.map_comp_right]
    · change
        ((continuousPathTrajectory P hP default).map
          (fun path (t : denseTimePhysicalSet I) ↦ path t)).map
            (DenseTimePath.pullbackPhysicalSet I) = _
      rw [continuousPathTrajectory_map_finiteDenseTimeSet P hP default hK I]
    · exact hEvaluate
    · exact DenseTimePath.measurable_pullbackPhysicalSet I
  · exact ContinuousPath.measurable_denseRestriction
  · exact Finset.measurable_restrict I

end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess

#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory_map_denseRestriction_map_restrict


