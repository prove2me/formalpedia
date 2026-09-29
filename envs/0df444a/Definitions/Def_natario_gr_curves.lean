-- Prove2me | Definitions.Def_natario_gr_curves
-- name    : natario_gr_curves
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T13:54:51.860233+00:00
-- url     : https://prove2.me/theorems/6bf037dc-7eac-4efa-afbc-8744eb7a3b6d
-- title:
--   Curves, geodesics, proper time, Jacobi fields and conjugate points
-- statement:
--   Curves in a coordinate spacetime: the geodesic equation, timelike, unit timelike, null and causal curves, proper time, geodesic completeness and the resulting notion of a singular spacetime, the covariant derivative of a vector field along a curve, the Jacobi equation and conjugate points along a timelike geodesic.
-- source:
--   J. Natário, Mathematical Relativity, arXiv:2003.02855, Chapter 4 (Singularity theorems), §§4.1, 4.3, 4.5

import Definitions.Def_natario_gr_core

open scoped ContDiff

/-!
# Curves, geodesics, Jacobi fields and conjugate points

Continuation of the coordinate framework for J. Natário, *Mathematical Relativity*
(arXiv:2003.02855), Chapter 4.
-/

namespace MathematicalRelativity

/-- Coordinate velocity of a curve. -/
noncomputable def vel (c : ℝ → Pt) (t : ℝ) : Pt := fun a => deriv (fun s => c s a) t

/-- Coordinate acceleration of a curve. -/
noncomputable def acc (c : ℝ → Pt) (t : ℝ) : Pt :=
  fun a => deriv (fun s => deriv (fun u => c u a) s) t

namespace Spacetime

variable (m : Spacetime)

/-- `c` solves the geodesic equation on the parameter set `I`. -/
def IsGeodesicOn (c : ℝ → Pt) (I : Set ℝ) : Prop :=
  (∀ a, ContDiffOn ℝ 2 (fun s => c s a) I) ∧
  ∀ t ∈ I, ∀ a, acc c t a
      + ∑ b, ∑ d, m.christoffel a b d (c t) * vel c t b * vel c t d = 0

/-- A future-pointing timelike geodesic. -/
def IsTimelikeGeodesicOn (c : ℝ → Pt) (I : Set ℝ) : Prop :=
  m.IsGeodesicOn c I ∧ ∀ t ∈ I, m.IsTimelike (c t) (vel c t) ∧ IsFuture (vel c t)

/-- A future-pointing timelike geodesic parameterized by proper time. -/
def IsUnitTimelikeGeodesicOn (c : ℝ → Pt) (I : Set ℝ) : Prop :=
  m.IsTimelikeGeodesicOn c I ∧ ∀ t ∈ I, m.ip (c t) (vel c t) (vel c t) = -1

/-- A future-pointing, affinely parameterized null geodesic. -/
def IsNullGeodesicOn (c : ℝ → Pt) (I : Set ℝ) : Prop :=
  m.IsGeodesicOn c I ∧ ∀ t ∈ I, m.IsNull (c t) (vel c t) ∧ IsFuture (vel c t)

/-- A future-pointing causal curve. -/
def IsCausalCurveOn (c : ℝ → Pt) (I : Set ℝ) : Prop :=
  (∀ a, ContDiffOn ℝ 1 (fun s => c s a) I) ∧
  ∀ t ∈ I, m.IsCausalVec (c t) (vel c t) ∧ IsFuture (vel c t)

/-- A future-pointing timelike curve. -/
def IsTimelikeCurveOn (c : ℝ → Pt) (I : Set ℝ) : Prop :=
  (∀ a, ContDiffOn ℝ 1 (fun s => c s a) I) ∧
  ∀ t ∈ I, m.IsTimelike (c t) (vel c t) ∧ IsFuture (vel c t)

/-- The proper time (Lorentzian length) of a timelike curve between two parameter values. -/
noncomputable def properTime (c : ℝ → Pt) (t₀ t₁ : ℝ) : ℝ :=
  ∫ t in t₀..t₁, Real.sqrt (-(m.ip (c t) (vel c t) (vel c t)))

/-- Geodesic completeness: every initial condition is the initial condition of a geodesic
defined for all values of the affine parameter. -/
def GeodesicallyComplete : Prop :=
  ∀ x v : Pt, ∃ c : ℝ → Pt, m.IsGeodesicOn c Set.univ ∧ c 0 = x ∧ vel c 0 = v

/-- A spacetime is singular when it is not geodesically complete (Natário, Def. 4.5.1). -/
def IsSingular : Prop := ¬ m.GeodesicallyComplete

/-- The covariant derivative along `c` of a vector field `Y` defined along `c`. -/
noncomputable def covDAlong (c Y : ℝ → Pt) (t : ℝ) : Pt :=
  fun a => deriv (fun s => Y s a) t + ∑ b, ∑ d, m.christoffel a b d (c t) * vel c t b * Y t d

/-- `Y` solves the Jacobi (geodesic deviation) equation `∇_X ∇_X Y = R(X, Y) X` along `c`. -/
def IsJacobiFieldOn (c Y : ℝ → Pt) (I : Set ℝ) : Prop :=
  (∀ a, ContDiffOn ℝ 2 (fun s => Y s a) I) ∧
  ∀ t ∈ I, ∀ a, m.covDAlong c (m.covDAlong c Y) t a
      = ∑ b, ∑ e, ∑ d, m.riemann a b e d (c t) * vel c t b * vel c t e * Y t d

/-- `c t₁` is conjugate to `c t₀` along the timelike geodesic `c`: there is a nontrivial
Jacobi field along `c` vanishing at both parameters (Natário, Def. 4.3.1). -/
def ConjugatePointAlong (c : ℝ → Pt) (t₀ t₁ : ℝ) : Prop :=
  ∃ Y : ℝ → Pt, m.IsJacobiFieldOn c Y (Set.Icc t₀ t₁) ∧
    (∃ t ∈ Set.Ioo t₀ t₁, Y t ≠ 0) ∧ Y t₀ = 0 ∧ Y t₁ = 0

end Spacetime

end MathematicalRelativity


