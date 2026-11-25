-- Prove2me | Definitions.Def_BasicResults_Spectral_Representation
-- name    : BasicResults_Spectral_Representation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:59:57.304012+00:00
-- url     : https://prove2.me/theorems/b7ce5724-1fe9-4ca6-b2aa-9031194b9503
-- title:
--   Representation
-- statement:
--   Definitions and structural lemmas for Representation, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Representation.lean

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_BasicResults_Spectral_RealProjection
set_option autoImplicit true
@[expose] public section
@[expose] public section
open ContinuousLinearMap SNumbers.Complexification RCLike
universe u
namespace SpectralRepresentation
variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
end SpectralRepresentation


