-- Prove2me | Definitions.Def_AccelNewtonDinkelbach_Supplement_LinearFractionalProgram
-- name    : AccelNewtonDinkelbach_Supplement_LinearFractionalProgram
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:58:54.130339+00:00
-- url     : https://prove2.me/theorems/0b22ede7-e6ee-4376-b2ef-efb8f53594e3
-- title:
--   Linear fractional program $(F)$ and its parametric value
-- statement:
--   A **linear fractional program** consists of a polyhedron $D\subseteq\mathbb R^m$ and vectors $c,d\in\mathbb R^m$. Its feasible points satisfy $x\in D$ and $d^\top x>0$, and its extended-real optimal value is
--
--   $$\inf\left\{\frac{c^\top x}{d^\top x}:x\in D,\ d^\top x>0\right\}.$$
--
--   The associated parametric value is $f(\delta)=\inf_{x\in D}(c-\delta d)^\top x$. The interface also records the root set, attainment, and recession directions of the whole polyhedron.
--
--   **Formalization Note** Vectors are functions on `Fin m`. Both infima are taken in `EReal`; hence an unbounded-below value is $-\infty$, not Lean's default real infimum.
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, program (F), p.9, and parametric function, p.10

import Mathlib

namespace AccelNewtonDinkelbach.Supplement

open scoped BigOperators

set_option autoImplicit false

/-- Data of the linear fractional program `(F)` in §3.2. -/
structure LinearFractionalProgram (m : ℕ) where
  D : Set (Fin m → ℝ)
  c : Fin m → ℝ
  d : Fin m → ℝ

namespace LinearFractionalProgram

variable {m : ℕ} (P : LinearFractionalProgram m)

/-- The Euclidean dot product in the coordinates used by the paper. -/
def dot (a x : Fin m → ℝ) : ℝ := ∑ i, a i * x i

/-- `D` is a polyhedron: a finite intersection of closed affine half-spaces. -/
def IsPolyhedron : Prop :=
  ∃ q : ℕ, ∃ A : Fin q → Fin m → ℝ, ∃ b : Fin q → ℝ,
    P.D = {x | ∀ i, b i ≤ dot (A i) x}

/-- Feasible points of `(F)` have a strictly positive denominator. -/
def Feasible (x : Fin m → ℝ) : Prop := x ∈ P.D ∧ 0 < dot P.d x

/-- The extended-real optimal value of `(F)`.  The value is `⊥` exactly when the
ratios are unbounded below (under the nonempty-feasible-set hypothesis used by the theorems). -/
noncomputable def value : EReal :=
  sInf {z : EReal | ∃ x, P.Feasible x ∧ z = ((dot P.c x / dot P.d x : ℝ) : EReal)}

/-- The parametric value `f(δ) = inf_{x∈D} (c-δd)ᵀx`. -/
noncomputable def paramValue (δ : ℝ) : EReal :=
  sInf {z : EReal | ∃ x ∈ P.D, z = ((dot P.c x - δ * dot P.d x : ℝ) : EReal)}

/-- The effective domain of the parametric value.  Since `(F)` has a feasible point,
`paramValue` can never be `⊤`; membership therefore only excludes `−∞`. -/
def paramDom : Set ℝ := {δ | P.paramValue δ ≠ ⊥}

/-- Roots of the parametric function. -/
def roots : Set ℝ := {δ | P.paramValue δ = 0}

/-- The value of `(F)` is attained at `x`. -/
def Attains (x : Fin m → ℝ) : Prop :=
  P.Feasible x ∧ P.value = ((dot P.c x / dot P.d x : ℝ) : EReal)

/-- A recession direction of the whole polyhedron `D`. -/
def IsRecessionDirection (r : Fin m → ℝ) : Prop :=
  ∀ x ∈ P.D, ∀ t : ℝ, 0 ≤ t → (fun i => x i + t * r i) ∈ P.D

end LinearFractionalProgram

end AccelNewtonDinkelbach.Supplement


