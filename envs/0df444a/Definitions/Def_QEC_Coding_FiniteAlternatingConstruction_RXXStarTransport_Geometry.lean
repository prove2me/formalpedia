-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T06:14:22.887206+00:00
-- url     : https://prove2.me/theorems/345d6d9b-4bb7-4b4c-8f3f-ca24295b7fc4
-- title:
--   Geometry
-- statement:
--   Definitions and structural lemmas for Geometry, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
abbrev XCoord (S : OddScale) {depth : Nat} (i : StepIndex depth) :=
  (state S i.val).presentation.X
abbrev QCoord (S : OddScale) {depth : Nat} (i : StepIndex depth) :=
  (state S i.val).presentation.Q
abbrev ZCoord (S : OddScale) {depth : Nat} (i : StepIndex depth) :=
  (state S i.val).presentation.Z
abbrev LocalPotential (S : OddScale) {depth : Nat} (i : StepIndex depth)
    (x : XCoord S i) := Word BDL26Field (DoubleCylinderVertex (state S i.val).presentation x S)
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
def incidentQ (x : XCoord S i) : Finset (QCoord S i) :=
  Finset.univ.filter fun q => (state S i.val).presentation.xq x q=true
def starQ (x : XCoord S i) : Finset (FamilyQ S depth i.succ) :=
  (incidentQ S depth i x).biUnion ((rxLq S depth i h).correctionRegion)
def star1 (x : XCoord S i) : Finset (FamilyQ S depth i.succ) :=
  (rxLx S depth i h).correctionRegion x ∪ starQ S depth i h x
def incidentZ (x : XCoord S i) : Finset (ZCoord S i) :=
  Finset.univ.filter fun z => ∃ q ∈ incidentQ S depth i x,
    (state S i.val).presentation.qz q z=true
def degreeZeroBlock (x : XCoord S i) : Finset (FamilyX S depth i.succ) :=
  Finset.univ.image fun v => rxDegreeZeroEquiv S depth i h ⟨x,v⟩
def boundaryVertex (x : XCoord S i) :
    SubdivisionBoundaryVertex (state S i.val).presentation x S :=
  subdivisionOriginalBoundaryVertex (state S i.val).presentation x S
    ((state S i.val).admissible.toTannerSquareAdmissible.xBoundaryRoot x)
def boundarySingleton (x : XCoord S i) : LocalPotential S i x :=
  Pi.single (0,(boundaryVertex S depth i x).val) 1
def boundaryGradient (x : XCoord S i) :
    Word BDL26Field (LocalRegionIndex ((rxLx S depth i h).correctionRegion x)) :=
  (rxContract S depth i h).rx_local_complexes.cxDelta0 x (boundarySingleton S depth i x)
def gradientError (x : XCoord S i) : Upper S depth i :=
  extendWordLinear ((rxLx S depth i h).correctionRegion x) (boundaryGradient S depth i h x)
end QEC.Coding.BDL26RXXStarTransport


