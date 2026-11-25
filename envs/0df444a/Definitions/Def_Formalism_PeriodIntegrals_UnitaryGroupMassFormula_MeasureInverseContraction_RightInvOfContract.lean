-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_RightInvOfContract
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_RightInvOfContract
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T04:54:48.948197+00:00
-- url     : https://prove2.me/theorems/ae6eae9d-2de1-468f-95ee-4fe2aad4577b
-- title:
--   Right Inv Of Contract
-- statement:
--   Definitions and structural lemmas for Right Inv Of Contract, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/RightInvOfContract.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Topology
open scoped ENNReal NNReal
namespace PI.NMeasInv.UnitaryGroupMassFormula
section Abs
attribute [local instance] Classical.propDecidable
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
def HaarOn (N : Subgroup G) (μ : Measure G) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ (N : Set G)ᶜ = 0 ∧ ∀ s ∈ N, μ.map (fun x => s * x) = μ
end Abs
end PI.NMeasInv.UnitaryGroupMassFormula


