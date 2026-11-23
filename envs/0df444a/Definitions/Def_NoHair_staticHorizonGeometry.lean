-- Prove2me | Definitions.Def_NoHair_staticHorizonGeometry
-- name    : NoHair_staticHorizonGeometry
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T09:14:14.753072+00:00
-- url     : https://prove2.me/theorems/74e3246e-095b-40db-b069-0a09c338e006
-- title:
--   Exact spatial static equations, regular horizon geometry, and conformal end charts
-- statement:
--   Spatial Hessian, raised gradient, and squared gradient norm of the lapse are formed using the spatial Levi-Civita connection. The static equations hold up to the horizon; the boundary data record a vanishing Hessian and strictly positive constant surface gravity. A spatial double chart parametrizes the physical portion of the flat double by a smooth isometry of the positive conformal metric.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_riemannianMassRigidity
import Definitions.Def_NoHair_staticCartesianRicci

noncomputable section

open Set
open scoped ContDiff

namespace NoHair

/-- Spatial covariant Hessian in the supplied coordinates. -/
def staticSpatialHessian (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (i j : Fin 3) (x : ADMPoint) : ℝ :=
  spatialADMPartial i (spatialADMPartial j N) x -
    ∑ k : Fin 3, spatialLeviCivita h x k i j * spatialADMPartial k N x

/-- The vector with index raised using the spatial metric. -/
def staticRaisedGradient (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (i : Fin 3) (x : ADMPoint) : ℝ :=
  ∑ j : Fin 3, (h x)⁻¹ i j * spatialADMPartial j N x

/-- The squared norm of the lapse gradient, equal on the horizon to squared surface gravity. -/
def staticLapseGradientSq (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (x : ADMPoint) : ℝ :=
  ∑ i : Fin 3, spatialADMPartial i N x * staticRaisedGradient N h i x

/-- The two spatial static vacuum equations up to and including the regular boundary. -/
def StaticSliceEquations (Ω : Set ADMPoint) (N : ADMPoint → ℝ)
    (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ x ∈ closure Ω,
    (∀ i j : Fin 3, staticSpatialHessian N h i j x = N x * spatialRicciTensor h x i j) ∧
    (∑ i : Fin 3, ∑ j : Fin 3, (h x)⁻¹ i j * staticSpatialHessian N h i j x) = 0

/-- Boundary conditions for reflection: the lapse Hessian vanishes and surface gravity is a
single positive constant on the horizon. The gradient of its square also vanishes there. -/
def StaticHorizonGeometry (Ω : Set ADMPoint) (N : ADMPoint → ℝ)
    (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ frontier Ω,
    (∀ i j, staticSpatialHessian N h i j x = 0) ∧
    staticLapseGradientSq N h x = κ^2 ∧ fderiv ℝ (staticLapseGradientSq N h) x = 0

/-- The physical part of Euclidean space after compactification and Euclidean rigidity. -/
def HasStaticSpatialDoubleChart (Ω : Set ADMPoint) (N : ADMPoint → ℝ)
    (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) (V : ADMPoint → ℝ) : Prop :=
  ∃ σ : OpenPartialHomeomorph ADMPoint ADMPoint,
    σ.source = {x | x ≠ 0 ∧ 0 < V x} ∧ σ.target = Ω ∧
    ContDiffOn ℝ ∞ σ σ.source ∧ ContDiffOn ℝ ∞ σ.symm σ.target ∧
    ∀ x ∈ σ.source, N (σ x) = V x ∧ ∀ v w : ADMPoint,
      (∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h (σ x) i j *
        (fderiv ℝ σ x v) i * (fderiv ℝ σ x w) j) = inner ℝ v w

/-- Geometric data for the Riemannian conformal doubling theorem on a single spatial end. -/
structure RegularRiemannianStaticEnd (Ω W : Set ADMPoint) (N : ADMPoint → ℝ)
    (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) : Prop where
  openSlice : IsOpen Ω
  connectedSlice : IsConnected Ω
  compactComplement : IsCompact Ωᶜ
  hasBoundary : (frontier Ω).Nonempty
  connectedBoundary : IsConnected (frontier Ω)
  openExtension : IsOpen W
  extendsAcross : closure Ω ⊆ W
  positiveSide : ∀ x ∈ W, x ∈ Ω ↔ 0 < N x
  regularLevel : ∀ x ∈ frontier Ω, N x = 0 ∧ fderiv ℝ N x ≠ 0
  smoothLapse : ContDiffOn ℝ ∞ N W
  smoothMetric : ∀ i j, ContDiffOn ℝ ∞ (fun x => h x i j) W
  positiveMetric : ∀ x ∈ W, (h x).PosDef
  falloff : ∀ k : ℕ, ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ x : ADMPoint, R < ‖x‖ →
    ‖iteratedFDeriv ℝ k (fun y => N y - 1) x‖ ≤ C / ‖x‖^(k+1) ∧
    ∀ i j, ‖iteratedFDeriv ℝ k (fun y => h y i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) x‖
      ≤ C / ‖x‖^(k+1)
  equations : StaticSliceEquations Ω N h
  horizon : StaticHorizonGeometry Ω N h

end NoHair


