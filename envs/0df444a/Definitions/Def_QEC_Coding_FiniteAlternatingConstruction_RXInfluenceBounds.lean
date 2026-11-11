-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T06:14:59.891966+00:00
-- url     : https://prove2.me/theorems/eeaa1c84-3bf9-47bc-bf41-01981e47906e
-- title:
--   RXInfluence Bounds
-- statement:
--   Definitions and structural lemmas for RXInfluence Bounds, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RXInfluenceBounds
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter BDL26RXCoarseInfluence BDL26BoundedValence
open BDL26GraphQuantitativeBounds BDL26RZMap1CoordinateBridge
open MultiscaleDecoder RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
section DirectedCounting
variable {V : Type} [Fintype V] [DecidableEq V]
def outNeighbors (G : DirectedGraph V) (u : V) : Finset V :=
  Finset.univ.filter fun v => G.edge u v = true
def forwardTwo (G : DirectedGraph V) (u : V) : Finset V :=
  insert u (outNeighbors G u ∪ (outNeighbors G u).biUnion (outNeighbors G))
end DirectedCounting
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)
def readers (p : FamilyZ S depth i.succ) : Finset (FamilyZ S depth i.castSucc) :=
  Finset.univ.filter fun z => p ∈ readRegion S depth i h z
def errorInfluence (e : (indexedFamily S depth).Cochain1 i.succ) :
    Finset (FamilyZ S depth i.castSucc) :=
  (hammingSupport e).biUnion (influence S depth i h)
def sigmaPlusError (sigma : (indexedFamily S depth).Syndrome i.succ)
    (e : (indexedFamily S depth).Cochain1 i.succ) : (indexedFamily S depth).Syndrome i.succ :=
  ⟨sigma.val + (indexedFamily S depth).coboundary1 i.succ e, by
    obtain ⟨a, ha⟩ := sigma.property
    exact ⟨a + e, by rw [map_add, ha]⟩⟩
end QEC.Coding.BDL26RXInfluenceBounds


