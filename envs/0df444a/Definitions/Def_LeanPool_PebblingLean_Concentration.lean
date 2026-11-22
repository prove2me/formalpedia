-- Prove2me | Definitions.Def_LeanPool_PebblingLean_Concentration
-- name    : LeanPool_PebblingLean_Concentration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:46:11.598418+00:00
-- url     : https://prove2.me/theorems/772b1b32-8a2d-4ab4-b79c-52fbf94fc9a0
-- title:
--   Concentration
-- statement:
--   Definitions and structural lemmas for Concentration, from Lior Pachter; LeanPool contributors's pinned Optimal Pebbling Number of the Hypercube development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_PebblingLean_FiniteProbability
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PebblingLean
namespace FiniteProbability
variable {Ω : Type*}
noncomputable def uniformProbabilityReal [Fintype Ω]
    (P : Ω → Prop) [DecidablePred P] : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (Fintype.card Ω : ℝ)
noncomputable def uniformExpectationReal [Fintype Ω] (X : Ω → ℝ) : ℝ :=
  (∑ ω : Ω, X ω) / (Fintype.card Ω : ℝ)
end FiniteProbability
end PebblingLean


