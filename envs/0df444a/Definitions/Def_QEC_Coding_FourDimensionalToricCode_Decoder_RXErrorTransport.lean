-- Prove2me | Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXErrorTransport
-- name    : QEC_Coding_FourDimensionalToricCode_Decoder_RXErrorTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T13:56:40.885039+00:00
-- url     : https://prove2.me/theorems/d37542d2-4e9c-4ff8-a55a-f468ba51c247
-- title:
--   RXError Transport
-- statement:
--   Definitions and structural lemmas for RXError Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXErrorTransport.lean

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
set_option autoImplicit false
namespace QEC
namespace Coding
namespace MultiscaleDecoder
namespace RXCoarseGraining
open scoped BigOperators
universe u v
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
namespace RXErrorTransport
structure RXQSectorRun
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz) where
  upperCorrection : D.family.Cochain1 i.succ
  upperSyndrome : D.family.Syndrome i.succ
  upperSyndrome_eq :
    D.family.coboundary1 i.succ upperCorrection = upperSyndrome
end RXErrorTransport
end RXCoarseGraining
end MultiscaleDecoder
end Coding
end QEC


