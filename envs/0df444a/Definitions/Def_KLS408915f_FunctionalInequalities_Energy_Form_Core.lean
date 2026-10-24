-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Core
-- name    : KLS408915f_FunctionalInequalities_Energy_Form_Core
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:46:07.441414+00:00
-- url     : https://prove2.me/theorems/949f196a-2dc1-4b0a-92b7-09c433893678
-- title:
--   Sequential cores and recovery sequences
-- statement:
--   `PreEnergy.HasRecoverySequenceAt energy x` means that some approximating sequence converges to x and its finite energies converge to the prescribed ENNReal value `energy x`. `PreEnergy.AgreesOnTests energy` means that the ambient functional equals the finite pre-energy on every realized concrete test, while `SequentiallyGenerates` means equality with the sequential relaxation. `IsSequentialCoreFor` packages the latter two exact equalities and does not itself assert density, closability, or a graph-norm core property.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Form/Core.lean#L29-L61 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Form.Core`, definition bundle `KLS408915f_FunctionalInequalities_Energy_Form_Core`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section
open Filter Topology
namespace FunctionalInequalities
namespace Energy
namespace PreEnergy
universe u v
variable {X : Type u} [TopologicalSpace X] (P : PreEnergy X)
/-- A recovery sequence at `x` converges to `x` in the ambient topology and has energies
converging to the prescribed extended value. -/
def HasRecoverySequenceAt (energy : Functional X) (x : X) : Prop :=
  ∃ f : P.ApproximatingSequence x,
    Tendsto (fun n ↦ (P.energy (f.1 n) : ENNReal)) atTop (𝓝 (energy x))
/-- A concrete test has the same energy before and after realization in the ambient space. -/
def AgreesOnTests (energy : Functional X) : Prop :=
  ∀ f : P.Test, energy (P.toAmbient f) = (P.energy f : ENNReal)
/-- The pre-energy sequentially generates an extended ambient energy. -/
def SequentiallyGenerates (energy : Functional X) : Prop :=
  P.sequentialRelaxation = energy
/-- A sequential form core both restricts the ambient energy correctly and generates it by
relaxation.

This project-specific name records the two exact equalities above. Identifying it with another
literature notion of graph-norm core is a theorem to be proved in the relevant analytic setting.
-/
structure IsSequentialCoreFor (energy : Functional X) : Prop where
  /-- The finite test energy is the restriction of the ambient energy. -/
  agreesOnTests : P.AgreesOnTests energy
  /-- Relaxing the test energy recovers the entire extended functional. -/
  sequentiallyGenerates : P.SequentiallyGenerates energy
end PreEnergy
end Energy
end FunctionalInequalities


