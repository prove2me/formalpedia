-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_ContinuousPathLawCleanV1
-- name    : MarkovProcess_V3HRepair_ContinuousPathLawCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T13:28:00.360682+00:00
-- url     : https://prove2.me/theorems/19c11ffc-0509-4977-b5b1-bb91234bb855
-- title:
--   Verified MarkovProcess source repair: ContinuousPathLawCleanV1
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess ContinuousPathLawCleanV1 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.ContinuousPathLawCleanV1 source SHA-256 6678ef57615ce4bcd261c9c22f13a9725a8f7cfe586878b7cd961a0e5d48330c. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names. Additional transparent proof aliases are appended after the source declarations for original frozen theorem targets 916ca016-99d6-4c15-9ba2-f568f718022d; these add no mathematical assumptions.

import Mathlib
import Definitions.Def_MarkovProcess_V3HRepair_WholePathWeakContinuityCleanV2
open Filter MeasureTheory ProbabilityTheory Topology
open scoped BoundedContinuousFunction ENNReal NNReal
namespace MarkovProcess
namespace SubMarkovKernelSemigroup
noncomputable section
open IsConservative
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [ProperSpace alpha]
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- **The path law is weakly continuous in the starting point.**  Read on the space of
probability measures on path space with its topology of convergence in distribution, the map
`x ↦ pathLaw P hP x` is continuous. -/
theorem IsFellerKernelSemigroup.continuous_pathLaw
    (hFeller : P.IsFellerKernelSemigroup) {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) :
    Continuous (IsConservative.pathLaw P hP) := by
  refine ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr fun F ↦ ?_
  exact IsFellerKernelSemigroup.continuous_integral_continuousProcess P hP hFeller hmom F

end
end SubMarkovKernelSemigroup
end MarkovProcess
#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuous_pathLaw

noncomputable def MarkovProcess.V3HRepairProof_916ca01699d64c159ba2f568f718022d :=
  @MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuous_pathLaw


