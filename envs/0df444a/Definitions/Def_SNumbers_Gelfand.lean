-- Prove2me | Definitions.Def_SNumbers_Gelfand
-- name    : SNumbers_Gelfand
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:34:20.862849+00:00
-- url     : https://prove2.me/theorems/eaa13b40-0277-406a-a6f2-9e4af01ec64c
-- title:
--   Gelfand
-- statement:
--   Definitions and structural lemmas for Gelfand, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
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
noncomputable def deviationFromRestriction (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) : ℝ :=
  ‖S.comp M.subtypeL‖
def gelfandSet (S : X →L[𝕜] Y) (n : ℕ) : Set ℝ :=
  {r | ∃ M : Submodule 𝕜 X,
      IsClosed (M : Set X) ∧
      Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal) ∧
      r = deviationFromRestriction S M}
noncomputable def gelfandNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  sInf (gelfandSet S n)
end SNumbers


