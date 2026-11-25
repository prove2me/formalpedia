-- Prove2me | Definitions.Def_SNumbers_SingularValuesFinDim
-- name    : SNumbers_SingularValuesFinDim
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T04:07:49.978525+00:00
-- url     : https://prove2.me/theorems/fc99ab22-b489-4156-8b4f-c3dfd318b318
-- title:
--   Singular Values Fin Dim
-- statement:
--   Definitions and structural lemmas for Singular Values Fin Dim, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/SingularValuesFinDim.lean

module
public import Definitions.Def_SNumbers_Uniqueness
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [FiniteDimensional 𝕜 H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [FiniteDimensional 𝕜 H₂]
variable [Nontrivial H₁] [Nontrivial H₂]
end SNumbers


