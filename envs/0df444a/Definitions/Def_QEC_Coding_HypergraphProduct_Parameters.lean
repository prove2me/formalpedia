-- Prove2me | Definitions.Def_QEC_Coding_HypergraphProduct_Parameters
-- name    : QEC_Coding_HypergraphProduct_Parameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:50:16.001808+00:00
-- url     : https://prove2.me/theorems/ff5b49f1-1460-48b8-b0f1-7144e1822b83
-- title:
--   Parameters
-- statement:
--   Definitions and structural lemmas for Parameters, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Parameters.lean

import Definitions.Def_QEC_Coding_HypergraphProduct_Core
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.LinearAlgebra.Matrix.Rank
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HypergraphProduct
universe u v
def firstCode
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    (D : Data F rowOne colOne rowTwo colTwo) : LinearCode F colOne :=
  parityCheckKernelCode (Matrix.toLin' D.first)
def secondCode
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) : LinearCode F colTwo :=
  parityCheckKernelCode (Matrix.toLin' D.second)
def firstTransposeCode
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    (D : Data F rowOne colOne rowTwo colTwo) : LinearCode F rowOne :=
  parityCheckKernelCode (Matrix.toLin' D.first.transpose)
def secondTransposeCode
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) : LinearCode F rowTwo :=
  parityCheckKernelCode (Matrix.toLin' D.second.transpose)
end QEC.Coding.HypergraphProduct


