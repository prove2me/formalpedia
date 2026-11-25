-- Prove2me | Definitions.Def_BasicResults_JohnIngredients
-- name    : BasicResults_JohnIngredients
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:27:02.34225+00:00
-- url     : https://prove2.me/theorems/2de573c4-4228-4f2f-b193-efb3e16b39fe
-- title:
--   John Ingredients
-- statement:
--   Definitions and structural lemmas for John Ingredients, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/JohnIngredients.lean

module
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Normed.Module.Span
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped InnerProductSpace ComplexConjugate
section SeminormHahnBanach
open RCLike
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
end SeminormHahnBanach
section TraceDuality
open ContinuousLinearMap
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E] [CompleteSpace E]
end TraceDuality


