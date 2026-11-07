-- Prove2me | Definitions.Def_QEC_Coding_HypergraphProduct_Locality
-- name    : QEC_Coding_HypergraphProduct_Locality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T03:06:46.234437+00:00
-- url     : https://prove2.me/theorems/f3322d86-43f1-4dac-bc54-b0770d0ff340
-- title:
--   Locality
-- statement:
--   Definitions and structural lemmas for Locality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Locality.lean

import Definitions.Def_QEC_Coding_HypergraphProduct_Core
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HypergraphProduct
universe u v
def rowWeight
    {F Row Col : Type*} [Zero F] [DecidableEq F] [Fintype Col]
    (H : Matrix Row Col F) (r : Row) : Nat :=
  HammingWeight (H r)
def columnWeight
    {F Row Col : Type*} [Zero F] [DecidableEq F] [Fintype Row]
    (H : Matrix Row Col F) (c : Col) : Nat :=
  HammingWeight (fun r => H r c)
def qubitDegree
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (q : QubitIndex rowOne colOne rowTwo colTwo) : Nat :=
  HammingWeight (boundary1 D (Pi.single q 1)) +
    HammingWeight (wordLinearMapTranspose (boundary2 D) (Pi.single q 1))
end QEC.Coding.HypergraphProduct


