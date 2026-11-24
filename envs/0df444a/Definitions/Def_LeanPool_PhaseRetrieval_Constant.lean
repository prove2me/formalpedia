-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_Constant
-- name    : LeanPool_PhaseRetrieval_Constant
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:04:08.881801+00:00
-- url     : https://prove2.me/theorems/ea7d2844-585f-496c-bad9-ea29057e31bf
-- title:
--   Constant
-- statement:
--   Definitions and structural lemmas for Constant, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Local
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalCore
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalHelpers
public import Mathlib.Tactic.NormNum.Parity
set_option autoImplicit true
@[expose] public section
@[expose] public section
open FockSPR MeasureTheory Complex Real Polynomial
noncomputable section
namespace FockSPR
def centeredPolynomial (p : Polynomial ℂ) : Polynomial ℂ :=
  p - Polynomial.C (p.eval 0)
end FockSPR


