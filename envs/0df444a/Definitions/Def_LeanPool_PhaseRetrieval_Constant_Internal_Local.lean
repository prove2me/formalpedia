-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Local
-- name    : LeanPool_PhaseRetrieval_Constant_Internal_Local
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:03:33.997368+00:00
-- url     : https://prove2.me/theorems/82231c31-3a37-4284-bf3a-778416c1abde
-- title:
--   Local
-- statement:
--   Definitions and structural lemmas for Local, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/Local.lean

module
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalHelpers
public import Mathlib.Tactic.NormNum.Parity
set_option autoImplicit true
@[expose] public section
@[expose] public section
open FockSPR MeasureTheory Complex Real Polynomial
noncomputable section
namespace FockSPR
end FockSPR


