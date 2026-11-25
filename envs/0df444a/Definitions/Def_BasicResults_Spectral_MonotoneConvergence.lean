-- Prove2me | Definitions.Def_BasicResults_Spectral_MonotoneConvergence
-- name    : BasicResults_Spectral_MonotoneConvergence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:27:10.469108+00:00
-- url     : https://prove2.me/theorems/8bf9293a-8eec-4ae1-8e09-e5c387c45328
-- title:
--   Monotone Convergence
-- statement:
--   Definitions and structural lemmas for Monotone Convergence, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MonotoneConvergence.lean

module
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
set_option autoImplicit true
@[expose] public section
@[expose] public section
open ContinuousLinearMap RCLike
open scoped InnerProductSpace
namespace SpectralRepresentation
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Nontrivial H]
end SpectralRepresentation


