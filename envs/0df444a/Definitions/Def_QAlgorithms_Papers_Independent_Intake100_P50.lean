-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P50
-- name    : QAlgorithms_Papers_Independent_Intake100_P50
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T13:39:41.221993+00:00
-- url     : https://prove2.me/theorems/58089ee5-07ff-45b1-9cb0-42d535d9d9e0
-- title:
--   Definitions for General Quantum Resource Theories: Distillation, Formation and Consistent Resource Measures
-- statement:
--   The objects the formalized statements of *General Quantum Resource Theories: Distillation, Formation and Consistent Resource Measures* (arXiv:2002.02458) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `boundedTracePairing`: arXiv:2002.02458v3, PDF p.4, (3): testing a normal density state against any bounded observable, using the trace-class/bounded-operator pairing.
--   - `stateBoundedWeakTopology`: arXiv:2002.02458v3, PDF p.4: the source's explicitly defined "weak operator topology" on density operators. All bounded observables are used, including the identity; the accepted compact-test weak-star topology is a different definition and is not substituted here.
-- source:
--   General Quantum Resource Theories: Distillation, Formation and Consistent Resource Measures, arXiv:2002.02458v3, https://arxiv.org/abs/2002.02458v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13

/-!
Kuroiwa and Yamasaki, arXiv:2002.02458v3.
The accepted trace-class definitions apply to arbitrary complete complex Hilbert
spaces; no separability or finite-dimensional restriction is imposed here.
Only Lemma 28 is drafted. The remaining assigned nodes are individually deferred
in HARD.md and GAPS.json. Compilation is pending the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P50

open QAlgorithms.Papers.Independent.Dependency50.P13

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- arXiv:2002.02458v3, PDF p.4, (3): testing a normal density state
against any bounded observable, using the trace-class/bounded-operator pairing. -/
def boundedTracePairing {I : Type*} (b : HilbertBasis I ℂ H)
    (rho : State b) (A : H →L[ℂ] H) : ℂ :=
  operatorTrace b (rho.val.val.comp A)

/-- arXiv:2002.02458v3, PDF p.4: the source's explicitly defined
"weak operator topology" on density operators. All bounded observables are
used, including the identity; the accepted compact-test weak-star topology
is a different definition and is not substituted here. -/
def stateBoundedWeakTopology {I : Type*} (b : HilbertBasis I ℂ H) :
    TopologicalSpace (State b) :=
  TopologicalSpace.induced (boundedTracePairing b) inferInstance

/-- The identity observable sees the trace-one normalization. -/
example {I : Type*} (b : HilbertBasis I ℂ H) (rho : State b) :
    boundedTracePairing b rho (ContinuousLinearMap.id ℂ H) = 1 := by
  simpa [boundedTracePairing] using rho.property.2

/-- The zero observable has zero expectation for every state. -/
example {I : Type*} (b : HilbertBasis I ℂ H) (rho : State b) :
    boundedTracePairing b rho (0 : H →L[ℂ] H) = 0 := by
  simp [boundedTracePairing, operatorTrace]

end QAlgorithms.Papers.Independent.Intake100.P50


