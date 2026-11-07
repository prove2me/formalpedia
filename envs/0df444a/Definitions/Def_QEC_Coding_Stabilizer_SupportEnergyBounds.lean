-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_SupportEnergyBounds
-- name    : QEC_Coding_Stabilizer_SupportEnergyBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:27:15.758202+00:00
-- url     : https://prove2.me/theorems/165e4faa-ae6e-47b3-964a-b4388e404e8c
-- title:
--   Support Energy Bounds
-- statement:
--   Definitions and structural lemmas for Support Energy Bounds, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/SupportEnergyBounds.lean

import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Coding
open PauliSymplectic
open scoped Classical
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace StabilizerCode.LocalStabilizerHamiltonian
variable {κ : Type*} [Fintype κ]
def incidentGeneratorUnion
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) : Finset κ :=
  R.biUnion H.incidentGenerators
end StabilizerCode.LocalStabilizerHamiltonian
end Coding
end QEC
namespace QEC
namespace Coding
namespace StabilizerCode
namespace LocalStabilizerHamiltonian
open PauliSymplectic
open scoped Classical
universe u
variable {κ : Type u} [Fintype κ]
end LocalStabilizerHamiltonian
end StabilizerCode
end Coding
end QEC


