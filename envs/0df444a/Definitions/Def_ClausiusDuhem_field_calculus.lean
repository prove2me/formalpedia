-- Prove2me | Definitions.Def_ClausiusDuhem_field_calculus
-- name    : ClausiusDuhem_field_calculus
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:27:36.907322+00:00
-- url     : https://prove2.me/theorems/3ac177ed-ae27-4a60-8f80-d960533e390e
-- title:
--   Cartesian vector calculus on $\mathbb R^3$ (Clausius–Duhem mission)
-- statement:
--   Vector calculus on physical space $\mathbb R^3$ in Cartesian coordinates $x=(x_0,x_1,x_2)$.
--
--   1. Partial derivative of a scalar field $f$: $\partial f/\partial x_j(x)$, the Fréchet derivative of $f$ at $x$ applied to the unit vector $e_j$.
--   2. Gradient $\nabla f = (\partial f/\partial x_0, \partial f/\partial x_1, \partial f/\partial x_2)$; divergence $\nabla\cdot F = \sum_j \partial F_j/\partial x_j$; dot product $u\cdot w=\sum_i u_i w_i$.
--   3. Velocity gradient $(\nabla \mathbf v)_{ij} = \partial v_i/\partial x_j$ and double contraction $A:B=\sum_{i,j}A_{ij}B_{ij}$.
--   4. Partial time derivative $\partial\varphi/\partial t$ and material time derivative
--   $$\dot\varphi = \frac{\partial\varphi}{\partial t} + \nabla\varphi\cdot\mathbf v.$$
--   5. Outward flux through the boundary of the box $\Omega=[a,b]=\prod_i[a_i,b_i]$:
--   $$\int_{\partial\Omega}F\cdot\mathbf n\,dA=\sum_{i}\Big(\int_{\{x_i=b_i\}}F_i\,dA-\int_{\{x_i=a_i\}}F_i\,dA\Big).$$
--
--   These are the operators in which every statement of the mission is written.
--
--   **Formalization Note** Space is `Fin 3 → ℝ`. Derivatives are Fréchet derivatives (Mathlib `fderiv`, `deriv`), which return $0$ at points of non-differentiability; all theorems of the mission assume enough differentiability that this convention is never used. Each box face is parametrized by the two remaining coordinates and carries two-dimensional Lebesgue measure.
-- source:
--   Wikipedia, "Clausius–Duhem inequality", revision oldid=1182390552, https://en.wikipedia.org/w/index.php?title=Clausius%E2%80%93Duhem_inequality&oldid=1182390552, sections "Clausius–Duhem inequality in terms of the specific entropy" (integral form, proof) and "Clausius–Duhem inequality in terms of specific internal energy" (index notation).

import Mathlib

/-!
Vector calculus on Euclidean 3-space `ℝ³ = Fin 3 → ℝ`, in Cartesian coordinates,
as used in the Wikipedia article "Clausius–Duhem inequality" (oldid=1182390552).
-/

namespace ClausiusDuhem

/-- Physical space `ℝ³`, with Cartesian coordinates `x 0, x 1, x 2`. -/
abbrev Space := Fin 3 → ℝ

/-- The partial derivative `∂f/∂x_j` of a scalar field `f` at the point `x`. -/
noncomputable def partialDeriv (f : Space → ℝ) (j : Fin 3) (x : Space) : ℝ :=
  fderiv ℝ f x (Pi.single j (1 : ℝ))

/-- The gradient `∇f(x) = (∂f/∂x_0, ∂f/∂x_1, ∂f/∂x_2)` of a scalar field. -/
noncomputable def grad (f : Space → ℝ) (x : Space) : Fin 3 → ℝ :=
  fun j => partialDeriv f j x

/-- The divergence `∇ · F(x) = ∑_j ∂F_j/∂x_j` of a vector field `F`. -/
noncomputable def div (F : Space → Fin 3 → ℝ) (x : Space) : ℝ :=
  ∑ j : Fin 3, partialDeriv (fun y => F y j) j x

/-- The Euclidean dot product `u · w = ∑_i u_i w_i`. -/
def dot (u w : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, u i * w i

/-- The velocity gradient `(∇v)_{ij} = ∂v_i/∂x_j` of a vector field `v`. -/
noncomputable def velocityGradient (v : Space → Fin 3 → ℝ) (x : Space) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => partialDeriv (fun y => v y i) j x

/-- The double contraction `A : B = ∑_{i,j} A_{ij} B_{ij}` of two second-order tensors. -/
def doubleDot (A B : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, A i j * B i j

/-- The partial time derivative `∂φ/∂t (t, x)` of a time-dependent scalar field. -/
noncomputable def timeDeriv (φ : ℝ → Space → ℝ) (t : ℝ) (x : Space) : ℝ :=
  deriv (fun τ => φ τ x) t

/-- The material time derivative `φ̇ = ∂φ/∂t + ∇φ · v` of a scalar field `φ`
following the velocity field `v`. -/
noncomputable def materialDeriv (φ : ℝ → Space → ℝ) (v : ℝ → Space → Fin 3 → ℝ)
    (t : ℝ) (x : Space) : ℝ :=
  timeDeriv φ t x + dot (grad (φ t) x) (v t x)

/-- The outward flux `∫_{∂Ω} F · n dA` of a vector field `F` through the boundary of the
closed rectangular box `Ω = [a, b] = ∏_i [a_i, b_i]`.  The face `x_i = b_i` has outward
normal `e_i` and the face `x_i = a_i` has outward normal `-e_i`; each face is parametrised by
the two remaining coordinates and carries two-dimensional Lebesgue (area) measure. -/
noncomputable def boxOutwardFlux (F : Space → Fin 3 → ℝ) (a b : Space) : ℝ :=
  ∑ i : Fin 3,
    ((∫ y in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (b i) y) i) -
      ∫ y in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (a i) y) i)

end ClausiusDuhem


