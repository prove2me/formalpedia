-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
-- name    : QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T00:13:46.535031+00:00
-- url     : https://prove2.me/theorems/54fd99ee-5014-4831-b26d-6ecfb08fa4dc
-- title:
--   Alternating Cochain
-- statement:
--   Definitions and structural lemmas for Alternating Cochain, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AlternatingCochain.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
set_option autoImplicit false
namespace QEC.Coding.BDL26AlternatingCochain
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26DecodingGraph
abbrev Field := BDL26FiniteTannerSquare.Field
noncomputable def nextMap0 (S : OddScale) (n : Nat) (C : ConstructionState) :
    Word Field C.presentation.X →ₗ[Field] Word Field (nextState S n C).presentation.X := by
  classical
  by_cases h : n % 2 = 0
  · exact Eq.mpr
      (congrArg (fun D : ConstructionState =>
        Word Field C.presentation.X →ₗ[Field] Word Field D.presentation.X)
        (show nextState S n C = rxState S C from if_pos h))
      (rxMap0Coord C.presentation S)
  · exact Eq.mpr
      (congrArg (fun D : ConstructionState =>
        Word Field C.presentation.X →ₗ[Field] Word Field D.presentation.X)
        (show nextState S n C = rzState S C from if_neg h))
      (rzMap0Coord C.presentation S)
noncomputable def nextMap1 (S : OddScale) (n : Nat) (C : ConstructionState) :
    Word Field C.presentation.Q →ₗ[Field] Word Field (nextState S n C).presentation.Q := by
  classical
  by_cases h : n % 2 = 0
  · exact Eq.mpr
      (congrArg (fun D : ConstructionState =>
        Word Field C.presentation.Q →ₗ[Field] Word Field D.presentation.Q)
        (show nextState S n C = rxState S C from if_pos h))
      (rxMap1Coord C.presentation S)
  · exact Eq.mpr
      (congrArg (fun D : ConstructionState =>
        Word Field C.presentation.Q →ₗ[Field] Word Field D.presentation.Q)
        (show nextState S n C = rzState S C from if_neg h))
      (map1Coord C.presentation C.admissible S)
noncomputable def nextMap2 (S : OddScale) (n : Nat) (C : ConstructionState) :
    Word Field C.presentation.Z →ₗ[Field] Word Field (nextState S n C).presentation.Z := by
  classical
  by_cases h : n % 2 = 0
  · exact Eq.mpr
      (congrArg (fun D : ConstructionState =>
        Word Field C.presentation.Z →ₗ[Field] Word Field D.presentation.Z)
        (show nextState S n C = rxState S C from if_pos h))
      (rxMap2Coord C.presentation S)
  · exact Eq.mpr
      (congrArg (fun D : ConstructionState =>
        Word Field C.presentation.Z →ₗ[Field] Word Field D.presentation.Z)
        (show nextState S n C = rzState S C from if_neg h))
      (map2Coord C.presentation C.admissible S)
noncomputable def stepMap0 (S : OddScale) (n : Nat) :
    Word Field (state S n).presentation.X →ₗ[Field]
      Word Field (state S (n + 1)).presentation.X := nextMap0 S n (state S n)
noncomputable def stepMap1 (S : OddScale) (n : Nat) :
    Word Field (state S n).presentation.Q →ₗ[Field]
      Word Field (state S (n + 1)).presentation.Q := nextMap1 S n (state S n)
noncomputable def stepMap2 (S : OddScale) (n : Nat) :
    Word Field (state S n).presentation.Z →ₗ[Field]
      Word Field (state S (n + 1)).presentation.Z := nextMap2 S n (state S n)
noncomputable def map0 (S : OddScale) (n : Nat) := finiteCoordinateComposite (stepMap0 S) n
noncomputable def map1 (S : OddScale) (n : Nat) := finiteCoordinateComposite (stepMap1 S) n
noncomputable def map2 (S : OddScale) (n : Nat) := finiteCoordinateComposite (stepMap2 S) n
end QEC.Coding.BDL26AlternatingCochain


