-- Prove2me | Definitions.Def_BallPlank_ShiftedPlanks
-- name    : BallPlank_ShiftedPlanks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:37:08.370536+00:00
-- url     : https://prove2.me/theorems/53202266-afb4-5046-b7cb-943e32ed7663
-- title:
--   Shifted Planks
-- statement:
--   Definitions and structural lemmas for Shifted Planks, from Arseniy Akopyan and Alexander Polyanskii (akopjan/Palomar-Bang-Ball; see pinned Apache-2.0 LICENSE and README.md)'s pinned A Short Proof of Ball's Plank Theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/ShiftedPlanks.lean

module
public import Definitions.Def_BallPlank_Planks
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped RealInnerProductSpace
open Classical
noncomputable section
namespace Planks
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι]
end Planks
end


