-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T06:10:33.731424+00:00
-- url     : https://prove2.me/theorems/cbace1b5-7985-4474-93c6-338d12a8c60d
-- title:
--   RXQBlock Transport
-- statement:
--   Definitions and structural lemmas for RXQBlock Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RXQBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
abbrev Data := rxData S depth i h
abbrev QCoord (S : OddScale) {depth : Nat} (i : StepIndex depth) :=
  (state S i.val).presentation.Q
abbrev XCoord (S : OddScale) {depth : Nat} (i : StepIndex depth) :=
  (state S i.val).presentation.X
abbrev ZCoord (S : OddScale) {depth : Nat} (i : StepIndex depth) :=
  (state S i.val).presentation.Z
abbrev Syn (S : OddScale) (depth : Nat) (i : StepIndex depth) :=
  (indexedFamily S depth).Cochain2 i.succ
def rootCoefficient (q : QCoord S i) (a b : Upper S depth i) : BDL26Field :=
  updated S depth i h a b
    (rxQVertexEquiv S depth i h q (0, Sum.inl (Sum.inl ()))).val
def lowerWord (q : QCoord S i) (a b : Upper S depth i) : Lower S depth i :=
  rootCoefficient S depth i h q a b • canonicalBasisWord q
def potential (_even : i.val % 2=0) : Potential S depth i := 0
def incidentZ (S : OddScale) {depth : Nat} (i : StepIndex depth)
    (q : QCoord S i) : Finset (ZCoord S i) :=
  Finset.univ.filter fun z => (state S i.val).presentation.qz q z=true
def twoCopyIncidentZ (q : QCoord S i) : Finset (FamilyZ S depth i.succ) :=
  ((incidentZ S i q).product (Finset.univ : Finset (Fin 2))).image
    (fun zc => ((Data S depth i h).induced.zPairEquiv zc).val)
def incidentWitness (S : OddScale) {depth : Nat} (i : StepIndex depth)
    (q : QCoord S i) : ZCoord S i :=
  ((state S i.val).admissible.toTannerSquareAdmissible.qzRoot q).val
end QEC.Coding.BDL26RXQBlockTransport


