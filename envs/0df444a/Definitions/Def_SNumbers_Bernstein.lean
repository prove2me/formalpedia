-- Prove2me | Definitions.Def_SNumbers_Bernstein
-- name    : SNumbers_Bernstein
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:43:59.541891+00:00
-- url     : https://prove2.me/theorems/abcb4a20-e976-4b37-9f6b-9811ef3aab61
-- title:
--   Bernstein
-- statement:
--   Definitions and structural lemmas for Bernstein, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.LinearAlgebra.Dimension.RankNullity
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
noncomputable def gainOnSubspace (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) : ℝ :=
  sInf {r | ∃ x : X, x ∈ M ∧ x ≠ 0 ∧ r = ‖S x‖ / ‖x‖}
def bernsteinSet (S : X →L[𝕜] Y) (n : ℕ) : Set ℝ :=
  {r | ∃ M : Submodule 𝕜 X,
      Module.rank 𝕜 M = (n + 1 : ℕ) ∧ r = gainOnSubspace S M}
noncomputable def bernsteinNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  sSup (bernsteinSet S n)
end SNumbers


