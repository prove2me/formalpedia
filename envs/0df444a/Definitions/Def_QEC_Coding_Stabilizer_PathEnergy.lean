-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
-- name    : QEC_Coding_Stabilizer_PathEnergy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:25:54.870764+00:00
-- url     : https://prove2.me/theorems/2508175f-c63a-4857-bed5-9c3965612740
-- title:
--   Path Energy
-- statement:
--   Definitions and structural lemmas for Path Energy, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean

import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Coding
open PauliSymplectic
open scoped Classical
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace PauliSymplectic
end PauliSymplectic
namespace PauliErrorPath
def reverse (γ : PauliErrorPath (ι := ι)) : PauliErrorPath (ι := ι) where
  increments := γ.increments.reverse.map binaryDagger
  step_weight_le_one := by
    intro step hstep
    rw [List.mem_map] at hstep
    obtain ⟨original, horiginal, rfl⟩ := hstep
    rw [weight_binaryDagger]
    exact γ.step_weight_le_one original (List.mem_reverse.mp horiginal)
end PauliErrorPath
namespace StabilizerCode.LocalStabilizerHamiltonian
def pathHeight
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (γ : PauliErrorPath (ι := ι)) : Nat :=
  (Finset.range (γ.increments.length + 1)).sup fun n =>
    H.btExcessEnergy (γ.stateAt n)
def logicalPathHeights
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) : Set Nat :=
  {height | ∃ γ : PauliErrorPath (ι := ι),
    H.HasLogicalEndpoint γ ∧ H.pathHeight γ = height}
def logicalEnergyBarrier
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) : Nat :=
  sInf H.logicalPathHeights
end StabilizerCode.LocalStabilizerHamiltonian
end Coding
end QEC


