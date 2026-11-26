-- Prove2me | Definitions.Def_MaxwellWave_calculus
-- name    : MaxwellWave_calculus
-- status  : Definition
-- author  : @LG
-- created : 2026-11-26T02:05:40.279048+00:00
-- url     : https://prove2.me/theorems/08aa4692-a6ad-4a53-9b2a-8fe13539763e
-- title:
--   Coordinate vector calculus on $\mathbb{R}^3$
-- statement:
--   Defines real coordinate triples and time-dependent fields on three-dimensional space, coordinate basis vectors, spatial partial derivatives, time derivatives, divergence, curl, and componentwise $C^2$ regularity. These are the exact operator conventions used by the Maxwell model.
-- source:
--   https://github.com/a-bekheet/lean-mwe/blob/617380ac3850f8c08b82617d1ca2e36090a25fa7/MaxwellWave/Maxwell.lean

import Mathlib
noncomputable section
open scoped BigOperators
namespace MaxwellWave
abbrev Vec3 := Fin 3 → ℝ
abbrev VectorField := Vec3 → Vec3
abbrev TDScalarField := ℝ → Vec3 → ℝ
abbrev TDVectorField := ℝ → Vec3 → Vec3
def basisVec (i : Fin 3) : Vec3 := Pi.single i 1
def partialDerivComp (F : VectorField) (i j : Fin 3) (x : Vec3) : ℝ :=
  fderiv ℝ (fun y => F y j) x (basisVec i)
def timeDerivComp (F : TDVectorField) (j : Fin 3) (t : ℝ) (x : Vec3) : ℝ :=
  deriv (fun s => F s x j) t
def divergence (F : VectorField) (x : Vec3) : ℝ :=
  ∑ i : Fin 3, partialDerivComp F i i x
def curl (F : VectorField) (x : Vec3) : Vec3 := fun k =>
  match k with
  | ⟨0, _⟩ => partialDerivComp F 1 2 x - partialDerivComp F 2 1 x
  | ⟨1, _⟩ => partialDerivComp F 2 0 x - partialDerivComp F 0 2 x
  | ⟨2, _⟩ => partialDerivComp F 0 1 x - partialDerivComp F 1 0 x
def IsC2Vector (F : VectorField) : Prop :=
  ∀ j : Fin 3, ContDiff ℝ 2 (fun x => F x j)
end MaxwellWave


