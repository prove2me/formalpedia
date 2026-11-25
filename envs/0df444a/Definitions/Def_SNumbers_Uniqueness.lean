-- Prove2me | Definitions.Def_SNumbers_Uniqueness
-- name    : SNumbers_Uniqueness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T04:03:43.045213+00:00
-- url     : https://prove2.me/theorems/26dbf6e0-b5b1-4f12-a9de-67f510b6296c
-- title:
--   Uniqueness
-- statement:
--   Definitions and structural lemmas for Uniqueness, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Uniqueness.lean

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_BasicResults_SVD
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open scoped Cardinal
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
end SNumbers


