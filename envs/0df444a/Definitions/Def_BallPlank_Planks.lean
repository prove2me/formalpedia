-- Prove2me | Definitions.Def_BallPlank_Planks
-- name    : BallPlank_Planks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:32:43.096124+00:00
-- url     : https://prove2.me/theorems/0ca33f01-c00a-49a2-94b0-e460feff64b2
-- title:
--   Planks
-- statement:
--   Definitions and structural lemmas for Planks, from Arseniy Akopyan and Alexander Polyanskii (akopjan/Palomar-Bang-Ball; see pinned Apache-2.0 LICENSE and README.md)'s pinned A Short Proof of Ball's Plank Theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/Planks.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped RealInnerProductSpace
open Classical
noncomputable section
namespace Planks
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι]
def plank {V : Type*} [AddCommGroup V] [Module ℝ V] (ℓ : Module.Dual ℝ V) : Set V :=
  {x | |ℓ x| < 1}
def objF (ℓ : ι → E →L[ℝ] ℝ) (y : ι → E) : ℝ := ∑ i, ((ℓ i (y i))⁻¹) ^ 2
def admissible (ℓ : ι → E →L[ℝ] ℝ) : Set (ι → E) :=
  {y | Orthonormal ℝ y ∧ ∀ i, 1 ≤ 2 * (Fintype.card ι : ℝ) * (ℓ i (y i)) ^ 2}
def rot (y : ι → E) (i j : ι) (t : ℝ) : ι → E := fun k =>
  if k = i then Real.cos t • y i + Real.sin t • y j
  else if k = j then (-Real.sin t) • y i + Real.cos t • y j
  else y k
def sgn (b : Bool) : ℝ := if b then 1 else -1
end Planks
end


