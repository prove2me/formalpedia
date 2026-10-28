-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Energy_Form_Core
-- name    : KLSModular_FunctionalInequalities_Energy_Form_Core
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:31:38.816544+00:00
-- url     : https://prove2.me/theorems/b744e313-2578-4970-9b76-48a1c977a015
-- title:
--   Sequential cores and recovery sequences
-- statement:
--   `PreEnergy.HasRecoverySequenceAt energy x` means that some approximating sequence converges to x and its finite energies converge to the prescribed ENNReal value `energy x`. `PreEnergy.AgreesOnTests energy` means that the ambient functional equals the finite pre-energy on every realized concrete test, while `SequentiallyGenerates` means equality with the sequential relaxation. `IsSequentialCoreFor` packages the latter two exact equalities and does not itself assert density, closability, or a graph-norm core property.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.Relaxation.Basic
--   import Mathlib.Topology.Instances.ENNReal.Lemmas
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def HasRecoverySequenceAt (energy : Functional X) (x : X) : Prop :=
--     ∃ f : P.ApproximatingSequence x,
--       Tendsto (fun n ↦ (P.energy (f.1 n) : ENNReal)) atTop (𝓝 (energy x))
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/Relaxation/Basic`](https://prove2.me/theorems/89c7a615-0c3d-45b2-8b60-f8b981228e0a).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Form/Core.lean) · `FunctionalInequalities.Energy.Form.Core` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Form/Core.lean#L29-L61 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Form.Core`, definition bundle `KLSModular_FunctionalInequalities_Energy_Form_Core`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

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


