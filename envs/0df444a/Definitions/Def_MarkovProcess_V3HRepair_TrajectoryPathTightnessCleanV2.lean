-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_TrajectoryPathTightnessCleanV2
-- name    : MarkovProcess_V3HRepair_TrajectoryPathTightnessCleanV2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T13:17:42.126389+00:00
-- url     : https://prove2.me/theorems/cf41948f-0dbc-4097-9b2c-5a0ac8bdbfc5
-- title:
--   Verified MarkovProcess source repair: TrajectoryPathTightnessCleanV2
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess TrajectoryPathTightnessCleanV2 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.TrajectoryPathTightnessCleanV2 source SHA-256 747fe261fc475efc34524e366802806a40e92ffbf5ed4363dbb8f86bff3fce58. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Continuity_PathTightness_ad16da33
import Definitions.Def_MarkovProcess_V3HRepair_ContinuousPathTightnessCleanV1
import Definitions.Def_MarkovProcess_V3HRepair_TrajectoryPathModulusCleanV2
open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- The process starts where it is told: from a starting point of a measurable set `A`, almost
every path has its time-zero value in `A`. -/
theorem IsConservative.measure_eval_zero_notMem_eq_zero (hK : P.KolmogorovRegular hP)
    {A : Set alpha} (hA : MeasurableSet A) {x : alpha} (hx : x ∈ A) :
    continuousProcess P hP x {omega : ContinuousPath alpha | omega 0 ∉ A} = 0 := by
  have hmeas : Measurable fun omega : ContinuousPath alpha ↦ omega (0 : ℝ≥0) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) 0
  have hval : (((continuousProcess P hP) x).map fun omega ↦ omega (0 : ℝ≥0)) Aᶜ = 0 := by
    rw [← Kernel.map_apply _ hmeas, IsConservative.continuousProcess_map_eval_zero P hP hK,
      Kernel.id_apply]
    rw [Measure.dirac_apply' _ hA.compl, Set.indicator_of_notMem (by simpa using hx)]
  rwa [Measure.map_apply hmeas hA.compl, Set.preimage_compl] at hval

variable [ProperSpace alpha]

/-- **Tightness of the path laws over a compact set of starting points.**  For a conservative
semigroup on a proper metric state space satisfying the intrinsic Kolmogorov moment criterion, the
family `{continuousProcess P hP x : x ∈ K0}` of laws on continuous-path space is tight whenever
`K0` is compact.

The two inputs are the modulus estimate `exists_measure_compl_modulusSet_le`, whose scale does not
depend on the starting point, and the fact that the process starts in `K0`. -/
theorem IsConservative.isTightMeasureSet_continuousProcess {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) {K0 : Set alpha} (hK0 : IsCompact K0) :
    IsTightMeasureSet ((fun x ↦ continuousProcess P hP x) '' K0) := by
  refine ContinuousPath.isTightMeasureSet_of_measure_compl_modulusSet_le hK0 ?_ ?_
  · rintro mu ⟨x, hx, rfl⟩
    exact IsConservative.measure_eval_zero_notMem_eq_zero P hP
      (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) hK0.isClosed.measurableSet hx
  · intro T r hr eps heps
    obtain ⟨delta, hdelta, hbound⟩ :=
      IsConservative.exists_measure_compl_modulusSet_le P hP hmom T hr heps
    refine ⟨delta, hdelta, ?_⟩
    rintro mu ⟨x, hx, rfl⟩
    exact hbound x

/-- Epsilon form of tightness: one compact set of paths carries all but `eps` of the mass from
every starting point of a compact set. -/
theorem IsConservative.exists_isCompact_measure_compl_le {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) {K0 : Set alpha} (hK0 : IsCompact K0) {eps : ℝ≥0∞}
    (heps : 0 < eps) :
    ∃ K : Set (ContinuousPath alpha), IsCompact K ∧
      ∀ x ∈ K0, continuousProcess P hP x Kᶜ ≤ eps := by
  obtain ⟨K, hKcompact, hKmass⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      (IsConservative.isTightMeasureSet_continuousProcess P hP hmom hK0) eps heps
  exact ⟨K, hKcompact, fun x hx ↦ hKmass _ ⟨x, hx, rfl⟩⟩

end

end SubMarkovKernelSemigroup

end MarkovProcess

#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsConservative.exists_isCompact_measure_compl_le


