-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_Energy
-- name    : QEC_Coding_Stabilizer_Energy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:22:39.609717+00:00
-- url     : https://prove2.me/theorems/6ed52998-9d6d-4617-a779-6d76b0c4c9a0
-- title:
--   Energy
-- statement:
--   Definitions and structural lemmas for Energy, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Energy.lean

import Definitions.Def_QEC_Coding_Stabilizer_ErrorPath
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Coding
namespace StabilizerCode
namespace LocalStabilizerHamiltonian
open PauliSymplectic
open scoped Classical
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
def violatedGenerators
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) : Finset κ :=
  Finset.univ.filter fun j => ¬ Commutes E (H.generators j)
def syndromeSupport
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) : Finset κ :=
  Finset.univ.filter fun j =>
    stabilizerSyndrome H.generators E j = 1
def syndromeWeight
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) : Nat :=
  (H.syndromeSupport E).card
def unitDefectEnergy
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) : Nat :=
  (H.violatedGenerators E).card
def btExcessEnergy
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) : Nat :=
  2 * H.unitDefectEnergy E
end LocalStabilizerHamiltonian
end StabilizerCode
end Coding
end QEC


