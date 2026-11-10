-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T05:02:11.561038+00:00
-- url     : https://prove2.me/theorems/4049b2bc-8840-4439-a709-871d22e265ec
-- title:
--   RXCoarse Influence
-- statement:
--   Definitions and structural lemmas for RXCoarse Influence, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RXCoarseInfluence
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable def basisSyndrome (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (q : FamilyQ S depth i.succ) : (indexedFamily S depth).Cochain2 i.succ :=
  (indexedFamily S depth).coboundary1 i.succ (canonicalBasisWord (F := BDL26Field) q)
noncomputable def sigmaPlus (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (sigma : (indexedFamily S depth).Syndrome i.succ) (q : FamilyQ S depth i.succ) :
    (indexedFamily S depth).Syndrome i.succ :=
  ⟨sigma.val + basisSyndrome S depth i q, by
    obtain ⟨e, he⟩ := sigma.property
    refine ⟨e + canonicalBasisWord q, ?_⟩
    change (indexedFamily S depth).coboundary1 i.succ (e + canonicalBasisWord q) =
      sigma.val + (indexedFamily S depth).coboundary1 i.succ (canonicalBasisWord q)
    rw [map_add, he]⟩
noncomputable def readRegion (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (z : FamilyZ S depth i.castSucc) : Finset (FamilyZ S depth i.succ) :=
  (xiIndexSet (rxData S depth i h).levelGraph.graph ((rxData S depth i h).coarseCenter z) 2).biUnion
    (fun v => (rxXiLocalComplex (rxData S depth i h)).syndromeRegion v)
noncomputable def influence (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (q : FamilyQ S depth i.succ) : Finset (FamilyZ S depth i.castSucc) :=
  Finset.univ.filter fun z =>
    ((hammingSupport (basisSyndrome S depth i q)) ∩ readRegion S depth i h z).Nonempty
end QEC.Coding.BDL26RXCoarseInfluence


