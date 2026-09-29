-- Prove2me | Definitions.Def_TongEM_wave_ops
-- name    : TongEM_wave_ops
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T01:09:54.114657+00:00
-- url     : https://prove2.me/theorems/a90bae4e-a028-477a-827e-251c6ef56580
-- title:
--   Second-order operators on $\mathbb{R}^3$: gradient, Laplacian and the wave operator $\Box_c$
-- statement:
--   This file adds the second-order differential operators that the derivation of the electromagnetic wave equation needs, on top of the platform's existing three-dimensional vector calculus (`Larmor_vec3`) and Maxwell equations (`Larmor_em_fields`).
--
--   Space is $\mathbb{R}^3$ with its Euclidean structure. For a scalar field $f$ on space, the partial derivative in the $j$-th coordinate direction is the derivative of $f$ along the $j$-th standard basis vector,
--   $$\partial_j f(x) = Df(x)[e_j],$$
--   the gradient is $\nabla f = (\partial_0f,\partial_1f,\partial_2f)$, and the Laplacian is
--   $$\nabla^2 f = \sum_{j=0}^{2}\partial_j\partial_j f .$$
--   The Laplacian of a vector field is taken componentwise, $(\nabla^2F)_i = \nabla^2(F_i)$.
--
--   For a time dependent vector field $F(t,x)$, the second time derivative $\partial_t^2F$ is the ordinary second derivative of $s\mapsto F(s,x)$ at fixed $x$, and the **wave operator** at speed $c$ is
--   $$\Box_c F = \frac{1}{c^2}\frac{\partial^2F}{\partial t^2} - \nabla^2 F,$$
--   with the same operator defined for scalar fields. Finally the file records the smoothness predicates used throughout: a field is smooth when it is $C^\infty$, jointly in time and position in the time dependent case.
--
--   Where a field fails to be differentiable, the underlying derivative returns the ambient junk value $0$; every theorem in this mission therefore states its smoothness hypothesis explicitly.
-- source:
--   David Tong, Lectures on Electromagnetism, University of Cambridge Mathematical Tripos Part IB, Lent Term 2015, http://www.damtp.cam.ac.uk/user/tong/em.html — Section 4.3 "And There Was Light", pp. 82–86, equations (4.12)–(4.14)

import Definitions.Def_Larmor_em_fields

/-!
# Second-order differential operators for electromagnetic waves

Support file for D. Tong, *Lectures on Electromagnetism* (Cambridge Mathematical
Tripos, Lent Term 2015), Section 4.3 "And There Was Light".

Space is `Larmor.Vec = EuclideanSpace ℝ (Fin 3)`, and the first-order operators
`Larmor.divg` and `Larmor.curl`, together with the Maxwell equations
`Larmor.IsMaxwell`, are taken from the already published files
`Def_Larmor_vec3` and `Def_Larmor_em_fields`.  This file only adds what the
wave equation needs on top of them: the partial derivative of a *scalar* field,
the gradient, the (componentwise) Laplacian, the second time derivative, the
wave operator `(1/c²) ∂²/∂t² - ∇²`, and smoothness predicates.
-/

namespace TongEM

open Larmor

/-- The partial derivative `∂f/∂xⱼ` of a scalar field on space, at the point `x`. -/
noncomputable def pd (j : Fin 3) (f : Vec → ℝ) (x : Vec) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single j 1)

/-- The gradient `∇f` of a scalar field on space. -/
noncomputable def grad (f : Vec → ℝ) (x : Vec) : Vec :=
  !₂[pd 0 f x, pd 1 f x, pd 2 f x]

/-- The Laplacian `∇²f = ∑ⱼ ∂²f/∂xⱼ²` of a scalar field on space. -/
noncomputable def lap (f : Vec → ℝ) (x : Vec) : ℝ := ∑ j, pd j (pd j f) x

/-- The Laplacian of a vector field on space, taken componentwise. -/
noncomputable def lapVec (F : Vec → Vec) (x : Vec) : Vec :=
  !₂[lap (fun y => F y 0) x, lap (fun y => F y 1) x, lap (fun y => F y 2) x]

/-- The second time derivative `∂²F/∂t²` of a time dependent vector field, at
fixed position. -/
noncomputable def dtt (F : ℝ → Vec → Vec) (t : ℝ) (x : Vec) : Vec :=
  deriv (fun s => deriv (fun r => F r x) s) t

/-- The wave operator `(1/c²) ∂²F/∂t² - ∇²F` applied to a time dependent vector
field. -/
noncomputable def box (c : ℝ) (F : ℝ → Vec → Vec) (t : ℝ) (x : Vec) : Vec :=
  (1 / c ^ 2) • dtt F t x - lapVec (F t) x

/-- The wave operator `(1/c²) ∂²u/∂t² - ∇²u` applied to a time dependent scalar
field. -/
noncomputable def boxScalar (c : ℝ) (u : ℝ → Vec → ℝ) (t : ℝ) (x : Vec) : ℝ :=
  (1 / c ^ 2) * deriv (fun s => deriv (fun r => u r x) s) t - lap (u t) x

/-- A scalar field on space is smooth if it is `C^∞`. -/
def SmoothS (f : Vec → ℝ) : Prop := ContDiff ℝ (⊤ : ℕ∞) f

/-- A vector field on space is smooth if it is `C^∞`. -/
def SmoothV (F : Vec → Vec) : Prop := ContDiff ℝ (⊤ : ℕ∞) F

/-- A time dependent vector field is smooth if it is `C^∞` jointly in time and
position. -/
def SmoothTV (F : ℝ → Vec → Vec) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec => F p.1 p.2)

end TongEM


