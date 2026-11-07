-- Prove2me | Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
-- name    : QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T03:23:06.513708+00:00
-- url     : https://prove2.me/theorems/6883c7b0-7d55-47bf-a9cb-e2dad87b65a5
-- title:
--   Energy Barrier Lower Bound
-- statement:
--   Definitions and structural lemmas for Energy Barrier Lower Bound, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
namespace BinarySquare
abbrev Grid (n : Nat) := Fin n → Fin n → ZMod 2
def flatten {n : Nat} (g : Grid n) : Word (ZMod 2) (Fin n × Fin n) :=
  fun q => g q.1 q.2
def horizontalDerivative {n : Nat} (g : Grid n) (y : Fin n) :
    Word (ZMod 2) (Fin (n - 1)) :=
  fun i => g y ⟨i.1 + 1, by omega⟩ + g y ⟨i.1, by omega⟩
def verticalDerivative {n : Nat} (g : Grid n) (x : Fin n) :
    Word (ZMod 2) (Fin (n - 1)) :=
  fun i => g ⟨i.1 + 1, by omega⟩ x + g ⟨i.1, by omega⟩ x
def openBoundaryLength {n : Nat} (g : Grid n) : Nat :=
  (∑ y : Fin n, HammingWeight (horizontalDerivative g y)) +
    ∑ x : Fin n, HammingWeight (verticalDerivative g x)
def fullRows {n : Nat} (g : Grid n) : Finset (Fin n) :=
  Finset.univ.filter fun y => ∀ x, g y x = 1
def emptyRows {n : Nat} (g : Grid n) : Finset (Fin n) :=
  Finset.univ.filter fun y => ∀ x, g y x = 0
def difference {n : Nat} (g h : Grid n) : Word (ZMod 2) (Fin n × Fin n) :=
  fun p => g p.1 p.2 + h p.1 p.2
def OneCellStep {n : Nat} (g h : Grid n) : Prop :=
  HammingWeight (difference g h) ≤ 1
end BinarySquare
variable {L : Nat} [NeZero L] [Fact (1 < L)]
abbrev finToPeriodic (i : Fin L) : ZMod L := ZMod.finEquiv L i
abbrev periodicToFin (a : ZMod L) : Fin L := (ZMod.finEquiv L).symm a
def primalSquareProjection (m : Word (ZMod 2) (Plaquette L)) :
    BinarySquare.Grid L :=
  fun y x => wordPairing (dualXYMembrane (finToPeriodic x) (finToPeriodic y)) m
def dualSquareProjection (m : Word (ZMod 2) (Plaquette L)) :
    BinarySquare.Grid L :=
  fun w z => wordPairing m (primalXYMembrane (finToPeriodic z) (finToPeriodic w))
def primalHorizontalLinkFiber (x y : ZMod L) :
    Word (ZMod 2) (Link L) :=
  ∑ z : ZMod L, ∑ w : ZMod L, cellWord (coord4 x y z w, .y)
def primalVerticalLinkFiber (x y : ZMod L) :
    Word (ZMod 2) (Link L) :=
  ∑ z : ZMod L, ∑ w : ZMod L, cellWord (coord4 x y z w, .x)
def primalHorizontalOpenFiber (q : Fin L × Fin (L - 1)) :
    Word (ZMod 2) (Link L) :=
  primalHorizontalLinkFiber
    (finToPeriodic (⟨q.2.1 + 1, by omega⟩ : Fin L))
    (finToPeriodic q.1)
def primalVerticalOpenFiber (q : Fin L × Fin (L - 1)) :
    Word (ZMod 2) (Link L) :=
  primalVerticalLinkFiber
    (finToPeriodic q.1)
    (finToPeriodic (⟨q.2.1 + 1, by omega⟩ : Fin L))
def dualHorizontalCubeFiber (z w : ZMod L) :
    Word (ZMod 2) (Cube L) :=
  ∑ x : ZMod L, ∑ y : ZMod L, cellWord (coord4 x y z w, .xyz)
def dualVerticalCubeFiber (z w : ZMod L) :
    Word (ZMod 2) (Cube L) :=
  ∑ x : ZMod L, ∑ y : ZMod L, cellWord (coord4 x y z w, .xyw)
def dualHorizontalOpenFiber (q : Fin L × Fin (L - 1)) :
    Word (ZMod 2) (Cube L) :=
  dualHorizontalCubeFiber
    (finToPeriodic (⟨q.2.1, by omega⟩ : Fin L))
    (finToPeriodic q.1)
def dualVerticalOpenFiber (q : Fin L × Fin (L - 1)) :
    Word (ZMod 2) (Cube L) :=
  dualVerticalCubeFiber
    (finToPeriodic q.1)
    (finToPeriodic (⟨q.2.1, by omega⟩ : Fin L))
def HasPrimalMembraneEndpoint
    (γ : PauliErrorPath (ι := Plaquette L)) : Prop :=
  ∃ z w : ZMod L, ∃ c : Word (ZMod 2) (Cube L),
    γ.endpoint.vector.zPart = primalXYMembrane z w + boundary3 c
def HasDualMembraneEndpoint
    (γ : PauliErrorPath (ι := Plaquette L)) : Prop :=
  ∃ x y : ZMod L, ∃ e : Word (ZMod 2) (Link L),
    γ.endpoint.vector.xPart =
      dualXYMembrane x y + wordLinearMapTranspose boundary2 e
def primalFullRowCount
    (γ : PauliErrorPath (ι := Plaquette L)) (n : Nat) : Nat :=
  (BinarySquare.fullRows
    (primalSquareProjection (γ.stateAt n).vector.zPart)).card
def dualFullRowCount
    (γ : PauliErrorPath (ι := Plaquette L)) (n : Nat) : Nat :=
  (BinarySquare.fullRows
    (dualSquareProjection (γ.stateAt n).vector.xPart)).card
end QEC.Coding.PeriodicCubical4


