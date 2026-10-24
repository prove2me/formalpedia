-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
-- name    : KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:34:08.569226+00:00
-- url     : https://prove2.me/theorems/dbc1778f-3f79-4e87-b022-2f18b14bfcbc
-- title:
--   Sequential relaxation of a finite pre-energy
-- statement:
--   `Energy.PreEnergy X` consists of a concrete test type, a realization into a topological ambient space X, and a finite nonnegative `NNReal` energy on concrete tests. `ApproximatingSequence P x` is a sequence of tests whose realizations tend to x, `sequenceEnergy` is the `ENNReal` liminf of its energies, and `sequentialRelaxation` is the infimum over all such sequences. `constantSequence` supplies the constant sequence at the realization of a concrete test; no lower semicontinuity claim is made for arbitrary topological spaces.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Relaxation/Basic.lean#L26-L74 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Relaxation.Basic`, definition bundle `KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section
open Filter Topology
namespace FunctionalInequalities
namespace Energy
universe u v
/-- A finite pre-energy carried by concrete tests and realized in an ambient space. -/
structure PreEnergy (X : Type u) where
  /-- The concrete tests on which the pre-energy is evaluated. -/
  Test : Type v
  /-- The realization of a concrete test in the ambient space. -/
  toAmbient : Test → X
  /-- The finite nonnegative energy of a concrete test. -/
  energy : Test → NNReal
namespace PreEnergy
variable {X : Type u} [TopologicalSpace X] (P : PreEnergy X)
/-- A sequence of concrete tests whose realizations converge to `x`. -/
def ApproximatingSequence (x : X) : Type max u v :=
  {f : ℕ → P.Test // Tendsto (fun n ↦ P.toAmbient (f n)) atTop (𝓝 x)}
/-- The energy `liminf` of an approximating sequence. -/
def sequenceEnergy {x : X} (f : P.ApproximatingSequence x) : ENNReal :=
  liminf (fun n ↦ (P.energy (f.1 n) : ENNReal)) atTop
/-- The sequential relaxation functional associated with the pre-energy.

Lower semicontinuity of this functional is not asserted for an arbitrary topological space.
-/
def sequentialRelaxation : Functional X where
  toFun x := ⨅ f : P.ApproximatingSequence x, P.sequenceEnergy f
/-- The constant sequence realizes a concrete test at its ambient image. -/
def constantSequence (f : P.Test) : P.ApproximatingSequence (P.toAmbient f) :=
  ⟨fun _ ↦ f, tendsto_const_nhds⟩
end PreEnergy
end Energy
end FunctionalInequalities


