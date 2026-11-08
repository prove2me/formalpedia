-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
-- name    : QEC_Coding_FiniteAlternatingConstruction_BoundedValence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T13:19:26.333704+00:00
-- url     : https://prove2.me/theorems/93410b4f-bae1-49aa-99b1-981a86f13617
-- title:
--   Bounded Valence
-- statement:
--   Definitions and structural lemmas for Bounded Valence, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BoundedValence.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
set_option autoImplicit false
namespace QEC.Coding.BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
def xDegree (P : TannerSquarePresentation) (x : P.X) : Nat :=
  Fintype.card {q : P.Q // P.xq x q = true}
def zDegree (P : TannerSquarePresentation) (z : P.Z) : Nat :=
  Fintype.card {q : P.Q // P.qz q z = true}
def qXDegree (P : TannerSquarePresentation) (q : P.Q) : Nat :=
  Fintype.card {x : P.X // P.xq x q = true}
def qZDegree (P : TannerSquarePresentation) (q : P.Q) : Nat :=
  Fintype.card {z : P.Z // P.qz q z = true}
def BoundedValence (P : TannerSquarePresentation) : Prop :=
  (∀ x, xDegree P x ≤ 7) ∧ (∀ z, zDegree P z ≤ 7) ∧
    ∀ q, qXDegree P q ≤ 4 ∧ qZDegree P q ≤ 4 ∧
      qXDegree P q + qZDegree P q ≤ 7
abbrev XQIncidentFace (P : TannerSquarePresentation) (e : XQEdge P) :=
  {f : P.Face // P.faceX f = e.1.1 ∧ ∃ i, P.faceQ f i = e.1.2}
abbrev QZIncidentFace (P : TannerSquarePresentation) (e : QZEdge P) :=
  {f : P.Face // P.faceZ f = e.1.2 ∧ ∃ i, P.faceQ f i = e.1.1}
end QEC.Coding.BDL26BoundedValence


