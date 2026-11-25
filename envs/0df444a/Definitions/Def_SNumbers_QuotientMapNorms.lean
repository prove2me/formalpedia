-- Prove2me | Definitions.Def_SNumbers_QuotientMapNorms
-- name    : SNumbers_QuotientMapNorms
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:30:35.724941+00:00
-- url     : https://prove2.me/theorems/68f73592-6428-4d8d-b0bf-efc24b77ec94
-- title:
--   Quotient Map Norms
-- statement:
--   Definitions and structural lemmas for Quotient Map Norms, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/QuotientMapNorms.lean

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Group.Quotient
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace ContinuousLinearMap
section UnitBall
variable {𝕜' : Type*} [DenselyNormedField 𝕜']
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜' E]
variable [SeminormedAddCommGroup F] [NormedSpace 𝕜' F]
end UnitBall
end ContinuousLinearMap
namespace Submodule
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {Y Z : Type*}
variable [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]
end Submodule


