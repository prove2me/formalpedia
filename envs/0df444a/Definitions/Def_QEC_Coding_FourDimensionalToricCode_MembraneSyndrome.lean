-- Prove2me | Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
-- name    : QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T03:13:50.110859+00:00
-- url     : https://prove2.me/theorems/217da86b-c8a4-4992-bf25-ce65f2ee4e65
-- title:
--   Membrane Syndrome
-- statement:
--   Definitions and structural lemmas for Membrane Syndrome, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]
abbrev PartialPrimalMembrane := Word (ZMod 2) (Plaquette L)
abbrev PartialDualMembrane := Word (ZMod 2) (Plaquette L)
def primalDefectLoop (m : PartialPrimalMembrane (L := L)) :
    Word (ZMod 2) (Link L) :=
  boundary2 m
def dualDefectLoop (m : PartialDualMembrane (L := L)) :
    Word (ZMod 2) (Cube L) :=
  wordLinearMapTranspose boundary3 m
def primalLoopLength (m : PartialPrimalMembrane (L := L)) : Nat :=
  HammingWeight (primalDefectLoop m)
def dualLoopLength (m : PartialDualMembrane (L := L)) : Nat :=
  HammingWeight (dualDefectLoop m)
def primalMembraneError (m : PartialPrimalMembrane (L := L)) :
    Binary (Plaquette L) :=
  cssZCheck m
def dualMembraneError (m : PartialDualMembrane (L := L)) :
    Binary (Plaquette L) :=
  cssXCheck m
end QEC.Coding.PeriodicCubical4


