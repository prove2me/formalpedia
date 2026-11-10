-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZConcreteParity
-- name    : QEC_Coding_FiniteAlternatingConstruction_RZConcreteParity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T01:22:13.99991+00:00
-- url     : https://prove2.me/theorems/c6fa1f53-5d72-47d5-9143-685b2fa3fc91
-- title:
--   RZConcrete Parity
-- statement:
--   Definitions and structural lemmas for RZConcrete Parity, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZConcreteParity.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
set_option autoImplicit false
namespace QEC.Coding.BDL26RZConcreteParity
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped BigOperators Classical
noncomputable def blockRegion (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) : Finset (RZZ P S) :=
  fiberRegion (fun t : RZZ P S => t.1) z
noncomputable def blockPart (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) : Word BDL26Field (RZZ P S) →ₗ[BDL26Field] Word BDL26Field (RZZ P S) :=
  fiberPart (fun t : RZZ P S => t.1) z
noncomputable def blockParity (P : TannerSquarePresentation) (S : OddScale)
    (r : Word BDL26Field (RZZ P S)) : Word BDL26Field P.Z :=
  fun z => ∑ v : ZDoubleCylinderVertex P z S, r ⟨z,v⟩
noncomputable def rootLift (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (b : BDL26Field) : Word BDL26Field (RZZ P S) :=
  map2Coord P A S (Pi.single z b)
end QEC.Coding.BDL26RZConcreteParity


