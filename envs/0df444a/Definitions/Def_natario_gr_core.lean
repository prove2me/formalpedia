-- Prove2me | Definitions.Def_natario_gr_core
-- name    : natario_gr_core
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T13:51:51.684098+00:00
-- url     : https://prove2.me/theorems/d2699955-a1ea-4489-8501-f766681fc999
-- title:
--   Lorentzian metrics in a global chart: curvature and energy conditions
-- statement:
--   The core of a coordinate framework for four-dimensional Lorentzian geometry. A spacetime is given by the components $g_{ij}$ of a metric in one global chart on $\mathbb{R}^4$: a smooth symmetric field which at each point is congruent to $\mathrm{diag}(-1,1,1,1)$, with $g_{00} < 0$ fixing a time orientation. The file defines the inverse metric, index raising and lowering, the Christoffel symbols of the Levi-Civita connection, the Riemann and Ricci tensors by their classical coordinate formulas, the classification of tangent vectors as timelike, null, causal or future-pointing, and the strong and null energy conditions.
-- source:
--   J. Natário, Mathematical Relativity, arXiv:2003.02855, Chapter 4 (Singularity theorems), §§4.1-4.2

import Mathlib

open scoped ContDiff

/-!
# Four-dimensional Lorentzian geometry in a global chart — core objects

Formalization framework for J. Natário, *Mathematical Relativity* (arXiv:2003.02855),
Chapter 4 (Singularity theorems).

A spacetime is modelled by the components of a Lorentzian metric in a single global
chart, so that points and tangent vectors are elements of `Fin 4 → ℝ` and all curvature
quantities are the classical coordinate expressions.
-/

namespace MathematicalRelativity

/-- A spacetime point, and also a tangent vector, in the global chart. -/
abbrev Pt : Type := Fin 4 → ℝ

/-- Partial derivative of `f` in the `i`-th coordinate direction. -/
noncomputable def pd (f : Pt → ℝ) (i : Fin 4) (x : Pt) : ℝ := fderiv ℝ f x (Pi.single i 1)

/-- The Minkowski signature matrix `diag(-1, 1, 1, 1)`. -/
def eta : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal (fun i => if i = 0 then -1 else 1)

/-- A four-dimensional spacetime described in a single global chart: a smooth field of
symmetric bilinear forms which is everywhere congruent to the Minkowski form (signature
`(-,+,+,+)`), time-oriented by requiring the coordinate direction `∂/∂x⁰` to be timelike. -/
structure Spacetime where
  g : Pt → Fin 4 → Fin 4 → ℝ
  smooth : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)
  symm : ∀ x i j, g x i j = g x j i
  lorentz : ∀ x, ∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P.det ∧
      P.transpose * (Matrix.of (g x)) * P = eta
  time_orient : ∀ x, g x 0 0 < 0

namespace Spacetime

variable (m : Spacetime)

/-- The metric components at `x`, as a matrix. -/
noncomputable def mat (x : Pt) : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of (m.g x)

/-- The inverse metric `g^{ij}`. -/
noncomputable def ginv (x : Pt) (i j : Fin 4) : ℝ := (m.mat x)⁻¹ i j

/-- The metric pairing `⟪u, v⟫ = g_{ij} u^i v^j` at `x`. -/
def ip (x : Pt) (u v : Pt) : ℝ := ∑ i, ∑ j, m.g x i j * u i * v j

/-- Index lowering: `V_i = g_{ij} V^j`. -/
def lower (x : Pt) (v : Pt) (i : Fin 4) : ℝ := ∑ j, m.g x i j * v j

/-- Index raising: `W^i = g^{ij} W_j`. -/
noncomputable def raise (x : Pt) (w : Fin 4 → ℝ) (i : Fin 4) : ℝ := ∑ j, m.ginv x i j * w j

/-- The Christoffel symbols `Γ^a_{bc}` of the Levi-Civita connection. -/
noncomputable def christoffel (a b c : Fin 4) (x : Pt) : ℝ :=
  (1/2 : ℝ) * ∑ d, m.ginv x a d *
    (pd (fun y => m.g y d c) b x + pd (fun y => m.g y d b) c x - pd (fun y => m.g y b c) d x)

/-- The Riemann curvature tensor `R^a_{bcd}`, normalised so that
`(R(u,v)w)^a = R^a_{bcd} w^b u^c v^d`. -/
noncomputable def riemann (a b c d : Fin 4) (x : Pt) : ℝ :=
  pd (m.christoffel a d b) c x - pd (m.christoffel a c b) d x
    + ∑ e, (m.christoffel a c e x * m.christoffel e d b x
              - m.christoffel a d e x * m.christoffel e c b x)

/-- The Riemann tensor with all indices down, `R_{abcd} = g_{ae} R^e_{bcd}`. -/
noncomputable def riemannLower (a b c d : Fin 4) (x : Pt) : ℝ :=
  ∑ e, m.g x a e * m.riemann e b c d x

/-- The Ricci tensor `R_{bd} = R^a_{bad}`. -/
noncomputable def ricci (b d : Fin 4) (x : Pt) : ℝ := ∑ a, m.riemann a b a d x

/-- The quadratic form `Ric(v, v)`. -/
noncomputable def ricciQuad (x v : Pt) : ℝ := ∑ i, ∑ j, m.ricci i j x * v i * v j

/-- `v` is timelike at `x`. -/
def IsTimelike (x v : Pt) : Prop := m.ip x v v < 0

/-- `v` is null (lightlike) at `x`. -/
def IsNull (x v : Pt) : Prop := m.ip x v v = 0 ∧ v ≠ 0

/-- `v` is causal at `x`. -/
def IsCausalVec (x v : Pt) : Prop := m.ip x v v ≤ 0 ∧ v ≠ 0

/-- `v` is future-pointing: its `x⁰`-component is positive.  For causal vectors this is a
genuine time orientation, because `∂/∂x⁰` is timelike. -/
def IsFuture (v : Pt) : Prop := 0 < v 0

/-- The strong energy condition, equivalently the timelike convergence condition:
`Ric(v, v) ≥ 0` for every timelike vector `v` (Natário, §4.2). -/
def StrongEnergyCondition : Prop := ∀ x v, m.IsTimelike x v → 0 ≤ m.ricciQuad x v

/-- The null energy condition: `Ric(v, v) ≥ 0` for every null vector `v` (Natário, §4.2). -/
def NullEnergyCondition : Prop := ∀ x v, m.IsNull x v → 0 ≤ m.ricciQuad x v

end Spacetime

end MathematicalRelativity


