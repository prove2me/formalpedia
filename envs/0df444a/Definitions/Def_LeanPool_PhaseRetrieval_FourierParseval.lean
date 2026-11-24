-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
-- name    : LeanPool_PhaseRetrieval_FourierParseval
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:58:44.502614+00:00
-- url     : https://prove2.me/theorems/637be2b1-26f8-44df-87b0-b203979dc246
-- title:
--   Fourier Parseval
-- statement:
--   Definitions and structural lemmas for Fourier Parseval, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/FourierParseval.lean

module
public import Mathlib.Analysis.Fourier.AddCircle
set_option autoImplicit true
@[expose] public section
open MeasureTheory Complex
open scoped BigOperators
namespace PhaseRetrieval
end PhaseRetrieval


