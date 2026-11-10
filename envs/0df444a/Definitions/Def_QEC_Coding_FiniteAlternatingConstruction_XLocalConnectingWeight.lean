-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
-- name    : QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T00:08:43.467718+00:00
-- url     : https://prove2.me/theorems/a2c507e8-e93c-4f9e-b4a7-72c535a3259f
-- title:
--   XLocal Connecting Weight
-- statement:
--   Definitions and structural lemmas for XLocal Connecting Weight, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
set_option autoImplicit false
namespace QEC.Coding.BDL26XLocalConnectingWeight
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26XLocalWeightParity
open scoped BigOperators Classical
abbrev Two := Fin 2
abbrev Neighbor (P : TannerSquarePresentation) (x : P.X) :=
  {q : P.Q // P.xq x q = true}
abbrev Output (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :=
  Σ q : Neighbor P x, QDoubleCylinderEdge P q.val S
def outputEdge (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (d : Output P x S) : DoubleCylinderEdge P x S :=
  qToXDoubleCylinderEdge P A d.1.val x d.1.property S d.2
noncomputable def connectingWeight
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (f : Word (ZMod 2) (DoubleCylinderEdge P x S)) : ℕ :=
  ∑ q : Neighbor P x, HammingWeight (rxXQDegreeOne P A q.val x q.property S f)
abbrev Fiber (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (e : DoubleCylinderEdge P x S) :=
  {d : Output P x S // outputEdge P A x S d = e}
def copiedQ (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DoubleCylinderEdge P x S → Option P.Q
  | .inl (_, .inl (old, _)) =>
      match old.val with
      | .inr qz => some qz.val.1
      | .inl _ => none
  | _ => none
def verticalZ (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DoubleCylinderEdge P x S → Option P.Z
  | .inr v =>
      match v.val with
      | .inl old =>
          match old.val with
          | .z z => some z
          | _ => none
      | _ => none
  | _ => none
end QEC.Coding.BDL26XLocalConnectingWeight


