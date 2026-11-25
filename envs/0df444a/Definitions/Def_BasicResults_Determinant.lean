-- Prove2me | Definitions.Def_BasicResults_Determinant
-- name    : BasicResults_Determinant
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:27:01.749383+00:00
-- url     : https://prove2.me/theorems/9f5e9fcd-5bde-429f-af8e-92e8647d2369
-- title:
--   Determinant
-- statement:
--   Definitions and structural lemmas for Determinant, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Determinant.lean

module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Determinant
set_option autoImplicit true
@[expose] public section
@[expose] public section
open LinearMap
open scoped ComplexConjugate
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]


