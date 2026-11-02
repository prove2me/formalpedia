-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_FellerMeasureSupportCleanV2
-- name    : MarkovProcess_V3HRepair_FellerMeasureSupportCleanV2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T09:48:41.848358+00:00
-- url     : https://prove2.me/theorems/4a0a94a1-32ef-43b1-a140-0029a62ffc91
-- title:
--   Verified MarkovProcess source repair: FellerMeasureSupportCleanV2
-- statement:
--   Continuous-path measures and kernels are identified by dense-time restrictions. Establish finite-dimensional approximation and integral shift convergence for conservative Feller semigroups.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream commit 1f8060caa137731fa08029592019eeaf9d997fe5; source-faithful adapted proof module V3HRepaired.FellerMeasureSupportCleanV2, archived SHA-256 cf0b70b3189d02222702d7a35b02ed9b10564692718d0843126c76254db2a762.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d

open MeasureTheory

namespace MarkovProcess
namespace Measure

noncomputable section

variable {alpha : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

/-- A measure on continuous-path space is determined by its pushforward to the fixed dense time
carrier. -/
theorem map_denseRestriction_injective :
    Function.Injective
      (fun mu : MeasureTheory.Measure (ContinuousPath alpha) ↦
        mu.map ContinuousPath.denseRestriction) := by
  intro mu nu h
  ext s hs
  have himage : MeasurableSet (ContinuousPath.denseRestriction '' s) :=
    ContinuousPath.measurableEmbedding_denseRestriction.measurableSet_image' hs
  have hmap := congrArg
    (fun rho : MeasureTheory.Measure (DenseTime → alpha) ↦
      rho (ContinuousPath.denseRestriction '' s)) h
  dsimp only at hmap
  rw [MeasureTheory.Measure.map_apply ContinuousPath.measurable_denseRestriction himage,
    MeasureTheory.Measure.map_apply ContinuousPath.measurable_denseRestriction himage] at hmap
  simpa only [ContinuousPath.denseRestriction_injective.preimage_image] using hmap

/-- Equality of continuous-path measures is equivalent to equality after restriction to the fixed
dense time carrier. -/
theorem map_denseRestriction_eq_iff
    {mu nu : MeasureTheory.Measure (ContinuousPath alpha)} :
    mu.map ContinuousPath.denseRestriction = nu.map ContinuousPath.denseRestriction ↔
      mu = nu := by
  constructor
  · intro h
    exact map_denseRestriction_injective (alpha := alpha) h
  · intro h
    exact congrArg
      (fun rho : MeasureTheory.Measure (ContinuousPath alpha) ↦
        rho.map ContinuousPath.denseRestriction) h

end
end Measure
end MarkovProcess

open MeasureTheory

namespace MarkovProcess
namespace Measure

noncomputable section

variable {index alpha : Type*} [MeasurableSpace alpha]

/-- Two measures on a product space agree if all their finite-coordinate pushforwards agree. -/
theorem eq_of_map_finiteRestriction_eq
    (mu nu : Measure (index → alpha)) [IsFiniteMeasure mu]
    (h : ∀ I : Finset index, mu.map I.restrict = nu.map I.restrict) :
    mu = nu := by
  let family : (I : Finset index) → Measure (I → alpha) :=
    fun I ↦ mu.map I.restrict
  have hmu : IsProjectiveLimit mu family := by
    intro I
    rfl
  have hnu : IsProjectiveLimit nu family := by
    intro I
    exact (h I).symm
  let (I : Finset index) : IsFiniteMeasure (family I) := by
    dsimp only [family]
    infer_instance
  exact hmu.unique hnu

end
end Measure
end MarkovProcess

open MeasureTheory ProbabilityTheory
open scoped NNReal CompactlySupported ZeroAtInfty
namespace MarkovProcess.SubMarkovKernelSemigroup
section Bound

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]

/-- A compact-test integral against a conservative finite dense-time law is bounded by the
test's canonical `C₀` norm. -/
theorem IsConservative.norm_integral_map_finiteSetKernel_pullbackPhysicalSet_le
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsConservative)
    (J : Finset DenseTime) (f : C_c(J → alpha, ℝ)) (y : alpha) :
    ‖∫ z, f z ∂(finiteSetKernel P (denseTimePhysicalSet J)).map
        (DenseTimePath.pullbackPhysicalSet J) y‖ ≤
      ‖PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f‖ := by
  let K := (finiteSetKernel P (denseTimePhysicalSet J)).map
    (DenseTimePath.pullbackPhysicalSet J)
  let : IsMarkovKernel K := by
    let : IsMarkovKernel (finiteSetKernel P (denseTimePhysicalSet J)) :=
      hP.isMarkovKernel_finiteSetKernel P (denseTimePhysicalSet J)
    exact Kernel.IsMarkovKernel.map _ (DenseTimePath.measurable_pullbackPhysicalSet J)
  let : IsProbabilityMeasure (K y) := IsMarkovKernel.isProbabilityMeasure y
  let f₀ : C₀(J → alpha, ℝ) :=
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
  change ‖∫ z, f z ∂K y‖ ≤ ‖f₀‖
  calc
    ‖∫ z, f z ∂K y‖ ≤ ‖f₀‖ * (K y).real Set.univ :=
      MeasureTheory.norm_integral_le_of_norm_le_const
        (ae_of_all _ fun z ↦ by
          simpa only [f₀,
            PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply] using!
            f₀.toBCF.norm_coe_le_norm z)
    _ = ‖f₀‖ := by
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one]

end Bound


end MarkovProcess.SubMarkovKernelSemigroup

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty CompactlySupported

namespace MarkovProcess

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [LocallyCompactSpace alpha]

omit [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] in
/-- Compact-test integrals of finitely many relative dense-time coordinates converge when the
deterministic shift times converge. The finite coordinate set may be empty. -/
theorem tendsto_integral_continuousPath_finiteDenseEvaluation_shift
    (mu : Measure (ContinuousPath alpha)) [IsFiniteMeasure mu]
    (s : NNReal) (q : ℕ → DenseTime)
    (hq : Tendsto (fun n ↦ DenseTime.castOrderEmbedding (q n)) atTop (nhds s))
    (J : Finset DenseTime) (f : C_c(J → alpha, ℝ)) :
    Tendsto
      (fun n ↦ ∫ omega, f (fun j : J ↦
        omega (DenseTime.castOrderEmbedding (q n) +
          DenseTime.castOrderEmbedding j)) ∂mu)
      atTop
      (nhds (∫ omega, f (fun j : J ↦
        omega (s + DenseTime.castOrderEmbedding j)) ∂mu)) := by
  let f₀ : C₀(J → alpha, ℝ) :=
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards [] with n
    exact (f.continuous.comp (ContinuousPath.continuous_finiteEvaluation
      (fun j : J ↦ DenseTime.castOrderEmbedding (q n) +
        DenseTime.castOrderEmbedding j))).aestronglyMeasurable
  · refine ⟨‖f₀‖, Filter.Eventually.of_forall fun n ↦ ?_⟩
    filter_upwards [] with omega
    simpa only [f₀, PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply,
      Real.norm_eq_abs] using! f₀.toBCF.norm_coe_le_norm
      (fun j : J ↦ omega (DenseTime.castOrderEmbedding (q n) +
        DenseTime.castOrderEmbedding j))
  · filter_upwards [] with omega
    apply f.continuous.continuousAt.tendsto.comp
    rw [tendsto_pi_nhds]
    intro j
    exact omega.continuous.continuousAt.tendsto.comp
      (hq.add tendsto_const_nhds)

end
end MarkovProcess

#print axioms MarkovProcess.Measure.map_denseRestriction_injective
#print axioms MarkovProcess.Measure.eq_of_map_finiteRestriction_eq
#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsConservative.norm_integral_map_finiteSetKernel_pullbackPhysicalSet_le
#print axioms MarkovProcess.tendsto_integral_continuousPath_finiteDenseEvaluation_shift


