-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_ContinuousProcessEvalMeasurableCleanV8
-- name    : MarkovProcess_V3HRepair_ContinuousProcessEvalMeasurableCleanV8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T10:03:22.495706+00:00
-- url     : https://prove2.me/theorems/238c84d3-b8d4-4074-ae9a-3783b8bb926a
-- title:
--   Verified MarkovProcess source repair: ContinuousProcessEvalMeasurableCleanV8
-- statement:
--   Coordinate evaluation marginals of dense-time and continuous-path Markov trajectories recover the transition kernel at each nonnegative time.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream commit 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.ContinuousProcessEvalMeasurableCleanV8 SHA-256 c36e9e8a2e74afaf7ad477709fc3232e5cd27489566160d33feb799e915c8af6. Only repaired import paths were translated to the published Definitions.Def_MarkovProcess_V3HRepair_* module names.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3HRepair_ExistsDenseTimeSequence
import Definitions.Def_MarkovProcess_V3HRepair_FiniteTimeKernelRestrictionCleanV3
import Definitions.Def_MarkovProcess_V3HRepair_FiniteTimeSingletonMarginalCleanV1

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty
namespace MarkovProcess
noncomputable section
/-- Nonnegative rational times admit a sequence converging to every nonnegative real time. -/
theorem exists_denseTime_seq_tendsto (t : NNReal) :
    ∃ q : ℕ → DenseTime,
      Tendsto (fun n ↦ DenseTime.castOrderEmbedding (q n)) atTop (nhds t) := by
  obtain ⟨q, _, _, hq⟩ := ContinuousPath.denseRange_castOrderEmbedding
    |>.exists_seq_strictAnti_tendsto
    DenseTime.castOrderEmbedding.monotone t
  exact ⟨q, by simpa only [Function.comp_apply] using! hq⟩

namespace SubMarkovKernelSemigroup
namespace IsConservative
variable {D α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
omit [StandardBorelSpace α] [Nonempty α] in
private theorem finiteTimeKernel_map_eval
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    {n : ℕ} (times : FiniteOrderedTimes n) (i : Fin n) :
    (finiteTimeKernel P times).map (fun path ↦ path i) = P (times i) := by
  let select : Fin 1 ↪o Fin n :=
    { toFun := fun _ ↦ i
      inj' := fun a b _ ↦ Subsingleton.elim a b
      map_rel_iff' := by
        intro a b
        constructor
        · intro _
          rw [Subsingleton.elim a b]
        · intro _
          exact le_rfl }
  have hfun :
      (fun path : Fin 1 → α ↦ path 0) ∘ FiniteOrderedTimes.restrictPath select =
        fun path : Fin n → α ↦ path i := by
    funext path
    rfl
  rw [← hfun, Kernel.map_comp_right]
  · rw [hP.finiteTimeKernel_map_restrictPath P times select]
    simpa only using! finiteTimeKernel_one_map_eval P (times.restrict select)
  · exact FiniteOrderedTimes.measurable_restrictPath select
  · exact measurable_pi_apply 0

/-- Every coordinate marginal of the dense-time trajectory is the transition kernel at its
embedded physical time. -/
theorem denseTimeTrajectory_map_eval
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (d : D) :
    (denseTimeTrajectory P hP e ι).map (fun path ↦ path d) = P (ι d) := by
  let k : ℕ := e.symm d
  let i : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  have hcoord : e i = d := by
    change e (e.symm d) = d
    exact e.apply_symm_apply d
  have hfun :
      (fun path : Fin (k + 1) → α ↦ path i) ∘
          denseTimeTrajectoryPrefix e (k + 1) =
        fun path : D → α ↦ path d := by
    funext path
    change path (e i) = path d
    rw [hcoord]
  rw [← hfun, Kernel.map_comp_right]
  · rw [denseTimeTrajectory_map_prefix P hP e ι (k + 1)]
    rw [denseTimePrefixKernel_eq_map, ← Kernel.map_comp_right]
    · have ht : ι (e i) ∈ denseTimePhysicalPrefix e ι (k + 1) := by
        rw [denseTimePhysicalPrefix, Finset.mem_map]
        refine ⟨e i, ?_, rfl⟩
        rw [CountableEnumeration.mem_prefix_iff, e.symm_apply_apply]
        exact i.isLt
      let t : denseTimePhysicalPrefix e ι (k + 1) := ⟨ι (e i), ht⟩
      have hprefix :
          (fun path : Fin (k + 1) → α ↦ path i) ∘
              denseTimePrefixReindex e ι (k + 1) =
            fun path : denseTimePhysicalPrefix e ι (k + 1) → α ↦ path t := by
        rfl
      rw [hprefix, finiteSetKernel_eq_map, ← Kernel.map_comp_right]
      · let j : Fin (denseTimePhysicalPrefix e ι (k + 1)).card :=
          ((denseTimePhysicalPrefix e ι (k + 1)).orderIsoOfFin rfl).symm t
        have hordered :
            (fun path : denseTimePhysicalPrefix e ι (k + 1) → α ↦ path t) ∘
                orderedPathToFiniteSet (denseTimePhysicalPrefix e ι (k + 1)) =
              fun path : Fin (denseTimePhysicalPrefix e ι (k + 1)).card → α ↦ path j := by
          rfl
        rw [hordered, finiteTimeKernel_map_eval P hP _ j]
        have hjtime :
            finiteSetTimes (denseTimePhysicalPrefix e ι (k + 1)) j = ι (e i) := by
          change ((((denseTimePhysicalPrefix e ι (k + 1)).orderIsoOfFin rfl) j :
            denseTimePhysicalPrefix e ι (k + 1)) : NNReal) = ι (e i)
          dsimp only [j]
          rw [OrderIso.apply_symm_apply]
        rw [hjtime, hcoord]
      · exact measurable_orderedPathToFiniteSet
          (denseTimePhysicalPrefix e ι (k + 1))
      · exact measurable_pi_apply t
    · exact measurable_denseTimePrefixReindex e ι (k + 1)
    · fun_prop
  · exact measurable_denseTimeTrajectoryPrefix e (k + 1)
  · fun_prop

end IsConservative
end SubMarkovKernelSemigroup

namespace SubMarkovKernelSemigroup
namespace IsConservative
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

/-- Every rational-time evaluation of the continuous-path transport has the prescribed
semigroup marginal, provided the canonical dense-time coordinate process satisfies the
parameterwise Kolmogorov condition. -/
theorem continuousPathTrajectory_map_eval
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (r : DenseTime) :
    (continuousPathTrajectory P hP default).map
        (fun path ↦ path (DenseTime.castOrderEmbedding r)) =
      P (DenseTime.castOrderEmbedding r) := by
  let kappa := denseTimeTrajectory P hP DenseTime.enumeration
    DenseTime.castOrderEmbedding.toEmbedding
  have hback :
      (continuousPathTrajectory P hP default).map ContinuousPath.denseRestriction = kappa := by
    exact Kernel.map_denseRestriction_toContinuousPathKernel_of_isKolmogorovCoordinate
      kappa default hK
  have hfun :
      (fun path : ContinuousPath alpha ↦ path (DenseTime.castOrderEmbedding r)) =
        (fun path : DenseTime → alpha ↦ path r) ∘ ContinuousPath.denseRestriction := by
    rfl
  rw [hfun, Kernel.map_comp_right]
  · rw [hback]
    exact denseTimeTrajectory_map_eval P hP DenseTime.enumeration
      DenseTime.castOrderEmbedding.toEmbedding r
  · exact ContinuousPath.measurable_denseRestriction
  · exact measurable_pi_apply r


/-- Feller time continuity upgrades the rational marginals of the continuous-path trajectory to
every nonnegative real time. -/
theorem continuousPathTrajectory_map_eval_nnreal
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hF : P.IsFellerKernelSemigroup) (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (t : NNReal) :
    (continuousPathTrajectory P hP default).map (fun path ↦ path t) = P t := by
  obtain ⟨q, hq⟩ := exists_denseTime_seq_tendsto t
  let : IsMarkovKernel (P t) := hP.isMarkovKernel t
  apply Kernel.ext
  intro x
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let K := continuousPathTrajectory P hP default
  let f0 : C₀(alpha, ℝ) :=
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
  have hpath : Tendsto
      (fun n ↦ ∫ omega, f (omega (DenseTime.castOrderEmbedding (q n))) ∂K x)
      atTop (nhds (∫ omega, f (omega t) ∂K x)) := by
    apply tendsto_integral_filter_of_norm_le_const
    · filter_upwards [] with n
      exact (f.continuous.comp
        (ContinuousPath.continuous_eval (alpha := alpha)
          (DenseTime.castOrderEmbedding (q n)))).aestronglyMeasurable
    · refine ⟨‖f0‖, Filter.Eventually.of_forall fun n ↦ ?_⟩
      filter_upwards [] with omega
      simpa only [f0, PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply,
        Real.norm_eq_abs] using! f0.toBCF.norm_coe_le_norm
        (omega (DenseTime.castOrderEmbedding (q n)))
    · filter_upwards [] with omega
      exact Filter.Tendsto.comp f.continuous.continuousAt
        (Filter.Tendsto.comp omega.continuous.continuousAt hq)
  have hsemigroup : Tendsto
      (fun n ↦ kernelIntegral (P (DenseTime.castOrderEmbedding (q n))) f x)
      atTop (nhds (kernelIntegral (P t) f x)) := by
    have hpair : Tendsto
        (fun n ↦ (DenseTime.castOrderEmbedding (q n), x)) atTop (nhds (t, x)) :=
      hq.prodMk_nhds tendsto_const_nhds
    have horbit :=
      (hF.c0Semigroup.continuous_apply_apply f0).tendsto (t, x) |>.comp hpair
    simpa only [IsFellerKernelSemigroup.c0Semigroup_apply_apply,
      PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply] using! horbit
  have heq : ∀ n,
      (∫ omega, f (omega (DenseTime.castOrderEmbedding (q n))) ∂K x) =
        kernelIntegral (P (DenseTime.castOrderEmbedding (q n))) f x := by
    intro n
    have hm := congrArg (fun L : Kernel alpha alpha ↦ L x)
      (continuousPathTrajectory_map_eval P hP default hK (q n))
    have hi := congrArg (fun mu : Measure alpha ↦ ∫ y, f y ∂mu) hm
    change (∫ y, f y ∂(K.map
      (ContinuousPath.eval (DenseTime.castOrderEmbedding (q n)))) x) =
        kernelIntegral (P (DenseTime.castOrderEmbedding (q n))) f x at hi
    have heval : Measurable (ContinuousPath.eval (alpha := alpha)
        (DenseTime.castOrderEmbedding (q n))) :=
      (ContinuousPath.continuous_eval (alpha := alpha)
        (DenseTime.castOrderEmbedding (q n))).borel_measurable.mono
          le_rfl (le_of_eq BorelSpace.measurable_eq)
    have hmap :
        (K.map (ContinuousPath.eval (DenseTime.castOrderEmbedding (q n)))) x =
          (K x).map (ContinuousPath.eval (DenseTime.castOrderEmbedding (q n))) :=
      Kernel.map_apply K heval x
    rw [hmap, integral_map] at hi
    · exact hi
    · exact heval.aemeasurable
    · exact f.continuous.aestronglyMeasurable
  have hsame :
      (fun n ↦ ∫ omega, f (omega (DenseTime.castOrderEmbedding (q n))) ∂K x) =
        fun n ↦ kernelIntegral (P (DenseTime.castOrderEmbedding (q n))) f x :=
    funext heq
  rw [hsame] at hpath
  have hlimit := tendsto_nhds_unique hpath hsemigroup
  change (∫ y, f y ∂(K.map (ContinuousPath.eval t)) x) =
    kernelIntegral (P t) f x
  have heval : Measurable (ContinuousPath.eval (alpha := alpha) t) :=
    (ContinuousPath.continuous_eval (alpha := alpha) t).borel_measurable.mono
      le_rfl (le_of_eq BorelSpace.measurable_eq)
  have hmap : (K.map (ContinuousPath.eval t)) x = (K x).map (ContinuousPath.eval t) :=
    Kernel.map_apply K heval x
  rw [hmap, integral_map]
  · exact hlimit
  · exact heval.aemeasurable
  · exact f.continuous.aestronglyMeasurable

end IsConservative
end SubMarkovKernelSemigroup
end
end MarkovProcess

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty
namespace MarkovProcess.SubMarkovKernelSemigroup
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- One-time marginal at every real time: evaluating the continuous-path process at time `t`
gives the transition kernel of `P` at `t`. -/
theorem IsFellerKernelSemigroup.continuousProcess_map_eval_nnreal
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) (t : NNReal) :
    (IsConservative.continuousProcess P hP).map (fun omega ↦ omega t) = P t :=
  IsConservative.continuousPathTrajectory_map_eval_nnreal P hP hFeller _ hK t


/-- A measurable real-valued observable evaluated at a deterministic time has the corresponding
transition-kernel integral. -/
theorem IsFellerKernelSemigroup.integral_eval_continuousProcess_of_measurable
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (t : NNReal) (x : alpha) {f : alpha → ℝ} (hf : Measurable f) :
    ∫ omega, f (omega t) ∂(IsConservative.continuousProcess P hP x) =
      ∫ y, f y ∂(P t x) := by
  have heval := ContinuousPath.measurable_coordinateProcess (alpha := alpha) t
  calc
    (∫ omega, f (omega t) ∂(IsConservative.continuousProcess P hP x)) =
        ∫ y, f y ∂Measure.map (fun omega : ContinuousPath alpha ↦ omega t)
          (IsConservative.continuousProcess P hP x) :=
      (integral_map heval.aemeasurable hf.stronglyMeasurable.aestronglyMeasurable).symm
    _ = ∫ y, f y ∂(P t x) := by
      change ∫ y, f y ∂Measure.map (ContinuousPath.coordinateProcess (alpha := alpha) t)
        (IsConservative.continuousProcess P hP x) = _
      rw [← Kernel.map_apply _ heval]
      exact congrArg (fun K : Kernel alpha alpha ↦ ∫ y, f y ∂K x)
        (hFeller.continuousProcess_map_eval_nnreal P hP hK t)


end MarkovProcess.SubMarkovKernelSemigroup
#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory_map_eval_nnreal
#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_eval_nnreal
#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.integral_eval_continuousProcess_of_measurable


