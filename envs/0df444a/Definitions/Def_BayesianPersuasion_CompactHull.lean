-- Prove2me | Definitions.Def_BayesianPersuasion_CompactHull
-- name    : BayesianPersuasion_CompactHull
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T08:57:45.756649+00:00
-- url     : https://prove2.me/theorems/6720e898-1365-4544-baac-f916dcedfef0
-- title:
--   Compact Hull
-- statement:
--   Definitions and structural lemmas for Compact Hull, from Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz; portions adapted from Daniel Lyng Econlib (Apache-2.0; see pinned LICENSE and source headers)'s pinned Optimal information and concavification in Bayesian persuasion development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/CompactHull.lean

module
public import Definitions.Def_BayesianPersuasion_Primitives
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set Finset
namespace BayesianPersuasion.Proof
instance belief_compact (ι : Type*) [Fintype ι] : CompactSpace (Belief ι) :=
  isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ ι)
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace E] [T2Space E] [ContinuousAdd E] [ContinuousSMul ℝ E]
end BayesianPersuasion.Proof


