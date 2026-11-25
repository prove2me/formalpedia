-- Prove2me | Definitions.Def_SNumbers_Approximation
-- name    : SNumbers_Approximation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:34:30.952685+00:00
-- url     : https://prove2.me/theorems/73482c8c-9034-45d5-8bc8-5be395fd7da9
-- title:
--   Approximation
-- statement:
--   Definitions and structural lemmas for Approximation, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open scoped Cardinal
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
def approximationSet (S : X →L[𝕜] Y) (n : ℕ) : Set ℝ :=
  {r | ∃ L : X →L[𝕜] Y, L.rank ≤ (n : Cardinal) ∧ r = ‖S - L‖}
noncomputable def approximationNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  sInf (approximationSet S n)
variable [CompleteSpace 𝕜]
noncomputable def approxFamily : Family 𝕜 :=
  fun {_X _Y} _ _ _ _ S n => approximationNumber S n
end SNumbers


