-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps
-- name    : QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T06:18:46.384833+00:00
-- url     : https://prove2.me/theorems/2fb816be-ee19-4f7e-aacd-df2c1ad51f40
-- title:
--   Steps
-- statement:
--   Definitions and structural lemmas for Steps, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Steps.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26RXDecoderAdapter BDL26RZDecoderAdapter
open BDL26RXCoarseInfluence BDL26RXInfluenceBounds MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
def rxPropagation (h : i.val % 2 = 0) (A : Finset (FamilyZ S depth i.succ)) :
    Finset (FamilyZ S depth i.castSucc) :=
  A.biUnion (readers S depth i h)
def rzBlockOwner (h : ¬ i.val % 2 = 0) (p : FamilyZ S depth i.succ) :
    FamilyZ S depth i.castSucc :=
  Classical.choose ((rzData S depth i h).coarseRegion_cover p)
def rzPropagation (h : ¬ i.val % 2 = 0) (A : Finset (FamilyZ S depth i.succ)) :
    Finset (FamilyZ S depth i.castSucc) := A.image (rzBlockOwner S depth i h)
def stepPropagation (A : Finset (FamilyZ S depth i.succ)) :
    Finset (FamilyZ S depth i.castSucc) :=
  if h : i.val % 2 = 0 then rxPropagation S depth i h A else rzPropagation S depth i h A
def stepFactor : Nat := if i.val % 2 = 0 then 57 else 1
end QEC.Coding.BDL26HistorySyndromeSensitivity


