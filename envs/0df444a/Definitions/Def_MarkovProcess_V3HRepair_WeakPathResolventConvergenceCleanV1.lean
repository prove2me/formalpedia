-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_WeakPathResolventConvergenceCleanV1
-- name    : MarkovProcess_V3HRepair_WeakPathResolventConvergenceCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T13:37:09.610799+00:00
-- url     : https://prove2.me/theorems/cf4f4bd4-c61c-423f-b405-750e113d4316
-- title:
--   Verified MarkovProcess source repair: WeakPathResolventConvergenceCleanV1
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess WeakPathResolventConvergenceCleanV1 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.WeakPathResolventConvergenceCleanV1 source SHA-256 c9e3a295051eea315c6509e00bcdb445be7242373e63e531c2599e1b0fd95d24. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names. Additional transparent proof aliases are appended after the source declarations for original frozen theorem targets d0611ca4-1afc-488d-b51e-c4173a51d643; these add no mathematical assumptions.

import Mathlib
import Definitions.Def_MarkovProcess_V3HRepair_TrotterKatoCleanV1
import Definitions.Def_MarkovProcess_V3HRepair_WeakPathConvergenceCleanV1
open Filter MeasureTheory ProbabilityTheory Topology
open scoped BoundedContinuousFunction ENNReal NNReal ZeroAtInfty
namespace MarkovProcess
namespace SubMarkovKernelSemigroup
noncomputable section
open IsConservative
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
 [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
 [Nonempty alpha] [ProperSpace alpha]
variable {iota : Type*} {l : Filter iota}
variable {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}
/-- **Weak convergence on path space from convergence of the resolvents.**  Combining the
Trotter--Kato theorem with the previous statement: strong convergence of the `C₀` resolvents at
one positive shift already forces the path laws to converge in distribution. -/
theorem tendsto_pathLaw_of_tendsto_resolvent
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hPc : ∀ i, (P i).IsConservative)
    (hQ : Q.IsFellerKernelSemigroup) (hQc : Q.IsConservative) {p q : ℝ} {M : ℝ≥0}
    (hPmom : ∀ i, (P i).HasKolmogorovMoments p q M) (hQmom : Q.HasKolmogorovMoments p q M)
    {mu : Semigroup.PositiveShift}
    (hres : ∀ f : C₀(alpha, ℝ), Tendsto (fun i ↦ (hP i).c0Semigroup.resolvent mu f) l
      (nhds (hQ.c0Semigroup.resolvent mu f))) (x : alpha) :
    Tendsto (fun i ↦ IsConservative.pathLaw (P i) (hPc i) x) l
      (nhds (IsConservative.pathLaw Q hQc x)) := by
  refine tendsto_pathLaw hP hPc hQ hQc hPmom hQmom (fun t f ↦ ?_) x
  exact Semigroup.StronglyContinuousContractionSemigroup.tendsto_operator_of_tendsto_resolvent
    hres f t

end
end SubMarkovKernelSemigroup
end MarkovProcess
#print axioms MarkovProcess.SubMarkovKernelSemigroup.tendsto_pathLaw_of_tendsto_resolvent

noncomputable def MarkovProcess.V3HRepairProof_d0611ca41afc488db51ec4173a51d643 :=
  @MarkovProcess.SubMarkovKernelSemigroup.tendsto_pathLaw_of_tendsto_resolvent


