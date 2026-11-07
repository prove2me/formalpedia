-- Prove2me | Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Restriction
-- name    : QEC_Coding_HypergraphProduct_Distance_Restriction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:28:01.713251+00:00
-- url     : https://prove2.me/theorems/b1ddd49f-c77b-4700-b766-2be104dab94f
-- title:
--   Restriction
-- statement:
--   Definitions and structural lemmas for Restriction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Restriction.lean

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Support
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HypergraphProduct
universe u v
def activeFirstColumns
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Zero F] [DecidableEq F]
    [Fintype rowOne] [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [Fintype colTwo]
    (z : Word F (QubitIndex rowOne colOne rowTwo colTwo)) : Finset colOne :=
  (hammingSupport z).biUnion fun q =>
    match q with
    | Sum.inl p => {p.1}
    | Sum.inr _ => ∅
def activeSecondRows
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Zero F] [DecidableEq F]
    [Fintype rowOne] [Fintype colOne]
    [Fintype rowTwo] [DecidableEq rowTwo] [Fintype colTwo]
    (z : Word F (QubitIndex rowOne colOne rowTwo colTwo)) : Finset rowTwo :=
  (hammingSupport z).biUnion fun q =>
    match q with
    | Sum.inl _ => ∅
    | Sum.inr p => {p.2}
def supportRestrictedData
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo] [Fintype colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo)) :
    Data (ZMod 2) rowOne {c // c ∈ activeFirstColumns z}
      {r // r ∈ activeSecondRows z} colTwo where
  first := restrictColumns D.first (activeFirstColumns z)
  second := fun r c => D.second r.1 c
end QEC.Coding.HypergraphProduct


