-- Prove2me | Definitions.Def_SNumbers_Hilbert
-- name    : SNumbers_Hilbert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:38:18.053788+00:00
-- url     : https://prove2.me/theorems/c5c4b8b7-a436-4a5c-a656-5d3d83a00186
-- title:
--   Hilbert
-- statement:
--   Definitions and structural lemmas for Hilbert, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open scoped Cardinal
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y W Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
abbrev L2 (𝕜 : Type*) [RCLike 𝕜] : Type _ := lp (fun _ : ℕ => 𝕜) 2
def hilbertSet (S : X →L[𝕜] Y) (n : ℕ) : Set ℝ :=
  {r | ∃ (A : L2 𝕜 →L[𝕜] X) (B : Y →L[𝕜] L2 𝕜),
      A ≠ 0 ∧ B ≠ 0 ∧
      r = approximationNumber (B.comp (S.comp A)) n / (‖B‖ * ‖A‖)}
noncomputable def hilbertNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  sSup (hilbertSet S n)
end SNumbers


