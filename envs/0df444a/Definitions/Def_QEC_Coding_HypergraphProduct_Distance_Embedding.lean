-- Prove2me | Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
-- name    : QEC_Coding_HypergraphProduct_Distance_Embedding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:29:14.37626+00:00
-- url     : https://prove2.me/theorems/2043f9f1-a6e0-4814-ad04-92529dfafe1b
-- title:
--   Embedding
-- statement:
--   Definitions and structural lemmas for Embedding, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Embedding.lean

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Restriction
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HypergraphProduct
universe u v
def supportRestrictedWord
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo] [Fintype colTwo]
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo)) :
    Word (ZMod 2)
      (QubitIndex rowOne {c // c ∈ activeFirstColumns z}
        {r // r ∈ activeSecondRows z} colTwo) :=
  fun q =>
    match q with
    | Sum.inl p => z (Sum.inl (p.1.1, p.2))
    | Sum.inr p => z (Sum.inr (p.1, p.2.1))
def supportExtendedWitness
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo] [Fintype colTwo]
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo))
    (w : Word (ZMod 2)
      (C2Index {c // c ∈ activeFirstColumns z}
        {r // r ∈ activeSecondRows z})) :
    Word (ZMod 2) (C2Index colOne rowTwo) :=
  fun p =>
    if hc : p.1 ∈ activeFirstColumns z then
      if hr : p.2 ∈ activeSecondRows z then
        w (⟨p.1, hc⟩, ⟨p.2, hr⟩)
      else 0
    else 0
end QEC.Coding.HypergraphProduct


