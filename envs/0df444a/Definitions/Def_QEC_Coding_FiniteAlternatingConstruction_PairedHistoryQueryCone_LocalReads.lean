-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_LocalReads
-- name    : QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_LocalReads
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T07:34:37.320233+00:00
-- url     : https://prove2.me/theorems/1113d5df-b64e-4581-a330-36338c17bd4e
-- title:
--   Local Reads
-- statement:
--   Definitions and structural lemmas for Local Reads, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/LocalReads.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26RXCoarseInfluence
open BDL26RXInfluenceBounds BDL26GraphQuantitativeBounds
open MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
abbrev Owners (S : OddScale) (depth : Nat) (i : StepIndex depth) :=
  RXVertex (state S i.val).presentation.X (state S i.val).presentation.Q
    (state S i.val).presentation.Z
def AgreeOn {I : Type} (A : Finset I) (s t : Word BDL26Field I) : Prop :=
  ∀ p ∈ A, s p = t p
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
def rxOwnerRead (h : i.val % 2 = 0) (v : Owners S depth i) :
    Finset (FamilyZ S depth i.succ) :=
  (xiIndexSet (rxData S depth i h).levelGraph.graph v 2).biUnion
    (fun w => (rxXiLocalComplex (rxData S depth i h)).syndromeRegion w)
def ownerRead (v : Owners S depth i) : Finset (FamilyZ S depth i.succ) :=
  if h : i.val % 2 = 0 then rxOwnerRead S depth i h v else
    match v with
    | .inl _ => ∅
    | .inr (.inl _) => ∅
    | .inr (.inr z) => (rzData S depth i h).coarseRegion z
def coarseRead (z : FamilyZ S depth i.castSucc) :
    Finset (FamilyZ S depth i.succ) :=
  if h : i.val % 2 = 0 then readRegion S depth i h z
  else (rzData S depth i h).coarseRegion z
def component (v : Owners S depth i)
    (s : Word BDL26Field (FamilyZ S depth i.succ)) :
    Word BDL26Field (FamilyQ S depth i.succ) :=
  if h : i.val % 2 = 0 then
    (rxLocalComponents (rxData S depth i h)).component v s
  else match v with
    | .inl _ => 0
    | .inr (.inl _) => 0
    | .inr (.inr z) => RZCoarseGraining.localCorrectionComponent
        (rzData S depth i h) (rzData_localTopCohomology S depth i h) z s
def affected (U : Finset (FamilyZ S depth i.succ)) : Finset (Owners S depth i) :=
  Finset.univ.filter fun v => ∃ p ∈ U, p ∈ ownerRead S depth i v
def correctionQueries (U : Finset (FamilyZ S depth i.succ)) :
    Finset (FamilyZ S depth i.succ) :=
  (affected S depth i U).biUnion (ownerRead S depth i)
def liftQueries (A : Finset (FamilyZ S depth i.castSucc)) :
    Finset (FamilyZ S depth i.succ) := A.biUnion (coarseRead S depth i)
end QEC.Coding.BDL26PairedHistoryQueryCone


