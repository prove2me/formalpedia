-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
-- name    : QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T01:49:26.50218+00:00
-- url     : https://prove2.me/theorems/87ae57da-c6fc-49d9-ac9e-185fe38d0a77
-- title:
--   Indexed Decoder
-- statement:
--   Definitions and structural lemmas for Indexed Decoder, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/IndexedDecoder.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Theorems.Thm_P2M_QEC_Coding_wordLinearMapTranspose_toLin__apply_6aba8976cbc7
import Theorems.Thm_QEC_Coding_BDL26AlternatingCochain_nextMap_commutes0
import Theorems.Thm_QEC_Coding_BDL26AlternatingCochain_nextMap_commutes1

set_option autoImplicit false
namespace QEC.Coding.BDL26IndexedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26ReplacementCochainMaps BDL26RZLocalReplacement BDL26RXLocalReplacement
open BDL26RZMap1CoordinateBridge
open MultiscaleDecoder BDL26AlternatingCochain
open scoped Classical
universe u
abbrev FamilyX (S : OddScale) (depth : Nat) (i : LevelIndex depth) :=
  (state S i.val).presentation.X
abbrev FamilyQ (S : OddScale) (depth : Nat) (i : LevelIndex depth) :=
  (state S i.val).presentation.Q
abbrev FamilyZ (S : OddScale) (depth : Nat) (i : LevelIndex depth) :=
  (state S i.val).presentation.Z
noncomputable def indexedFamily (S : OddScale) (depth : Nat) :
    BDL26CochainFamily depth (FamilyX S depth) (FamilyQ S depth) (FamilyZ S depth) where
  complex := fun i => BDL26LevelTwoDecoder.presentationComplex (state S i.val).presentation
theorem indexedFamily_coboundary0 (S : OddScale) (depth : Nat) (i : LevelIndex depth) :
    (indexedFamily S depth).coboundary0 i =
      tannerCoboundary0 (state S i.val).presentation := by
  apply LinearMap.ext
  intro e
  funext q
  exact wordLinearMapTranspose_toLin'_apply _ e q
theorem indexedFamily_coboundary1 (S : OddScale) (depth : Nat) (i : LevelIndex depth) :
    (indexedFamily S depth).coboundary1 i =
      tannerCoboundary1 (state S i.val).presentation := by
  apply LinearMap.ext
  intro e
  funext z
  exact wordLinearMapTranspose_toLin'_apply _ e z
noncomputable def indexedEdgeMap (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    BDL26CochainMap (indexedFamily S depth) i where
  map0 := stepMap0 S i.val
  map1 := stepMap1 S i.val
  map2 := stepMap2 S i.val
  commutes_coboundary0 := by
    rw [indexedFamily_coboundary0, indexedFamily_coboundary0]
    exact nextMap_commutes0 S i.val (state S i.val)
  commutes_coboundary1 := by
    rw [indexedFamily_coboundary1, indexedFamily_coboundary1]
    exact nextMap_commutes1 S i.val (state S i.val)
noncomputable def indexedDecoderData (S : OddScale) (depth : Nat) :
    BDL26DecoderData depth (FamilyX S depth) (FamilyQ S depth) (FamilyZ S depth) where
  family := indexedFamily S depth
  rxMap := indexedEdgeMap S depth
  rzMap := indexedEdgeMap S depth
end QEC.Coding.BDL26IndexedDecoder


