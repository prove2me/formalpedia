-- Prove2me | Definitions.Def_MaxwellWave_wave_ops
-- name    : MaxwellWave_wave_ops
-- status  : Definition
-- author  : @LG
-- created : 2026-11-26T02:13:28.753203+00:00
-- url     : https://prove2.me/theorems/b3cc277d-2b58-4bb6-bb21-f3d66745079e
-- title:
--   MaxwellWave: second-derivative and Laplacian operators
-- statement:
--   The second-order differential operators of the MaxwellWave vector-calculus layer, completing the first-order operators (partial derivative of a component, divergence, curl) introduced in `MaxwellWave_calculus`. For a scalar field $f:\mathbb R^3\to\mathbb R$ and a vector field $F:\mathbb R^3\to\mathbb R^3$, it defines the spatial partial derivative $\partial_i f$, the second partial $\partial_i^2 f$, the mixed component derivative $\partial_i\partial_i F_j$, the gradient $\nabla f$, the scalar Laplacian $\nabla^2 f=\sum_i \partial_i^2 f$, and the componentwise vector Laplacian $(\nabla^2 F)_j=\sum_i \partial_i^2 F_j$. Time derivatives of a time-dependent field are defined componentwise by `deriv`: `timeDerivComp2` is the second time derivative $\partial_t^2 F_j$. All derivatives are Fréchet derivatives (`fderiv`) evaluated on the standard basis vector `basisVec i`, and $C^2$ smoothness is expressed through `ContDiff ℝ 2`. These operators are the spatial part of the wave equations derived in this mission.
-- source:
--   https://github.com/a-bekheet/lean-mwe/blob/617380ac3850f8c08b82617d1ca2e36090a25fa7/MaxwellWave/VectorCalculus.lean#L28-L94

import Definitions.Def_MaxwellWave_calculus
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open scoped BigOperators
namespace MaxwellWave

abbrev ScalarField := Vec3 → ℝ

def partialDeriv (f : ScalarField) (i : Fin 3) (x : Vec3) : ℝ :=
  fderiv ℝ f x (basisVec i)

def partialDeriv2 (f : ScalarField) (i : Fin 3) (x : Vec3) : ℝ :=
  fderiv ℝ (fun y => partialDeriv f i y) x (basisVec i)

def partialDerivComp2 (F : VectorField) (i j : Fin 3) (x : Vec3) : ℝ :=
  fderiv ℝ (fun y => partialDerivComp F i j y) x (basisVec i)

def timeDeriv (f : TDScalarField) (t : ℝ) (x : Vec3) : ℝ :=
  deriv (fun s => f s x) t

def timeDeriv2 (f : TDScalarField) (t : ℝ) (x : Vec3) : ℝ :=
  deriv (fun s => timeDeriv f s x) t

def timeDerivComp2 (F : TDVectorField) (j : Fin 3) (t : ℝ) (x : Vec3) : ℝ :=
  deriv (fun s => timeDerivComp F j s x) t

def gradient (f : ScalarField) (x : Vec3) : Vec3 :=
  fun i => partialDeriv f i x

def scalarLaplacian (f : ScalarField) (x : Vec3) : ℝ :=
  ∑ i : Fin 3, partialDeriv2 f i x

def vectorLaplacian (F : VectorField) (x : Vec3) : Vec3 := fun j =>
  ∑ i : Fin 3, partialDerivComp2 F i j x

def IsC2Scalar (f : ScalarField) : Prop := ContDiff ℝ 2 f

scoped notation "∇" => gradient
scoped notation "∇⬝" => divergence
scoped notation "∇×" => curl
scoped notation "∇²ₛ" => scalarLaplacian
scoped notation "∇²" => vectorLaplacian

end MaxwellWave


