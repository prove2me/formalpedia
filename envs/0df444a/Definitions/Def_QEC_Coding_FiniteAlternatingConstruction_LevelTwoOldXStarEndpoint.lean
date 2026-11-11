-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoOldXStarEndpoint
-- name    : QEC_Coding_FiniteAlternatingConstruction_LevelTwoOldXStarEndpoint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T16:23:44.936897+00:00
-- url     : https://prove2.me/theorems/c7b19c9c-66be-47e0-bdc1-659d76b5cd62
-- title:
--   Level Two Old XStar Endpoint
-- statement:
--   Definitions and structural lemmas for Level Two Old XStar Endpoint, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26LevelTwoOldXStarEndpoint
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder BDL26DecodingGraph
open scoped Classical BigOperators
abbrev F := BDL26FiniteTannerSquare.Field
abbrev Seed := baseTannerSquarePresentation
abbrev P (S : OddScale) := levelOnePresentation S
abbrev C (S : OddScale) := levelTwoPresentation S
abbrev W1 (S : OddScale) := Word F (RX1 Seed S)
abbrev V1 (S : OddScale) := Word F (RX0 Seed S)
def Neighborhood (S : OddScale) (x : BaseX) : Finset (RX1 Seed S) :=
  Finset.univ.filter fun q => match q with
    | .inl e => e.1 = x
    | .inr v => Seed.xq x v.1 = true
def outsideMask (S : OddScale) (y : BaseX) (w : W1 S) : W1 S := fun r =>
  match r with
  | .inl e => if e.1=y then w r else 0
  | .inr _ => 0
def localLift (S : OddScale) (x : BaseX)
    (f : Word F (DoubleCylinderVertex Seed x S)) : V1 S := fun u =>
  if h : u.1=x then f (h ▸ u.2) else 0
def firstSearch (S : OddScale) (s : Word F (C S).Z) :=
  search (fun w => executableLocal S w &&
    decide (executableSyndrome S w=toExecutableSyndrome S s)) (allWords (ExecutableQ S))
def nativeRZQFintype (B : TannerSquarePresentation) (S : OddScale) :
    Fintype (RZQ B S) := inferInstance
local instance oldXActualQFintype (S : OddScale) : Fintype (C S).Q :=
  (C S).data.qFintype
def oldXLift (S : OddScale) (g : Word F (P S).X) : Word F (C S).X := fun u =>
  match u with
  | .inl _ => 0
  | .inr (x,c) => if c=0 then g x else 0
end QEC.Coding.BDL26LevelTwoOldXStarEndpoint


