-- Prove2me | Definitions.Def_BasicResults_Spectral_RealProjection
-- name    : BasicResults_Spectral_RealProjection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:56:18.523662+00:00
-- url     : https://prove2.me/theorems/9d08303e-5f74-4ae5-a4f7-f774bcef1fd2
-- title:
--   Real Projection
-- statement:
--   Definitions and structural lemmas for Real Projection, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/RealProjection.lean

module
public import Definitions.Def_BasicResults_Spectral_Complexification
public import Definitions.Def_BasicResults_Spectral_Projection
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SNumbers.Complexification ContinuousLinearMap
namespace SpectralRepresentation
variable {H₁ H₂ : Type*}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
end SpectralRepresentation


