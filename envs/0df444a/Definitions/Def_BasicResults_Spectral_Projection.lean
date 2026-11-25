-- Prove2me | Definitions.Def_BasicResults_Spectral_Projection
-- name    : BasicResults_Spectral_Projection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:42:39.815961+00:00
-- url     : https://prove2.me/theorems/64f4d0f8-5a42-4de7-8eeb-d7cc45691a63
-- title:
--   Projection
-- statement:
--   Definitions and structural lemmas for Projection, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Projection.lean

module
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Definitions.Def_BasicResults_Spectral_MonotoneConvergence
set_option autoImplicit true
@[expose] public section
@[expose] public section
open ContinuousLinearMap
namespace SpectralRepresentation
noncomputable def stepDown (t : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  max 0 (min 1 (1 + ((n : ℝ) + 1) * (s - t)))
open Filter Topology
open scoped InnerProductSpace
variable {H₁ H₂ : Type*}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
end SpectralRepresentation


