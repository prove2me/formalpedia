-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_MissingMathlib_Poincare
-- name    : LeanPool_PhaseRetrieval_Constant_Internal_MissingMathlib_Poincare
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:58:44.003799+00:00
-- url     : https://prove2.me/theorems/f31f8763-58ea-4ed6-9b03-11fd0a469ba8
-- title:
--   Poincare
-- statement:
--   Definitions and structural lemmas for Poincare, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/MissingMathlib/Poincare.lean

module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity.Finset
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory Real Set intervalIntegral Filter
noncomputable section
namespace FockSPR
namespace MissingMathlib
end MissingMathlib
end FockSPR


