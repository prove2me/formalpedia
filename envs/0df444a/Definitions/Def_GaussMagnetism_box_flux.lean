-- Prove2me | Definitions.Def_GaussMagnetism_box_flux
-- name    : GaussMagnetism_box_flux
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-27T18:58:21.628695+00:00
-- url     : https://prove2.me/theorems/91ff56f5-c0cd-4338-8395-a820c1717c5c
-- title:
--   Outward flux of a vector field through the boundary of a box in $\mathbb R^3$
-- statement:
--   Let $F=(F_0,F_1,F_2):\mathbb R^3\to\mathbb R^3$ be a vector field and let $a,b\in\mathbb R^3$ with $a_i<b_i$ for $i=0,1,2$. The **outward flux** of $F$ through the boundary of the box $\Omega=[a_0,b_0]\times[a_1,b_1]\times[a_2,b_2]$ is the surface integral
--
--   $$\Phi_F(a,b)=\oint_{\partial\Omega}F\cdot d\mathbf S,$$
--
--   where $d\mathbf S$ points along the outward unit normal. The boundary $\partial\Omega$ consists of six rectangular faces; on the face $x_i=b_i$ the outward normal is $+e_i$ and on the face $x_i=a_i$ it is $-e_i$. Hence
--
--   $$\Phi_F(a,b)=\int_{a_1}^{b_1}\!\!\int_{a_2}^{b_2}\big[F_0(b_0,y,z)-F_0(a_0,y,z)\big]\,dz\,dy+\int_{a_0}^{b_0}\!\!\int_{a_2}^{b_2}\big[F_1(x,b_1,z)-F_1(x,a_1,z)\big]\,dz\,dx+\int_{a_0}^{b_0}\!\!\int_{a_1}^{b_1}\big[F_2(x,y,b_2)-F_2(x,y,a_2)\big]\,dy\,dx.$$
--
--   Box boundaries are the closed surfaces used in this mission to state the integral form of Gauss's law for magnetism (the net magnetic flux through a closed surface is zero).
--
--   **Formalization Note** Space is `Larmor.Vec` $=$ `EuclideanSpace ℝ (Fin 3)` from the published definition `Larmor_vec3`. The integrals are Lean interval integrals; if an integrand is not integrable Lean returns $0$, so the value is meaningful for continuous $F$ (all theorems using it assume $F$ is at least $C^1$). The formula is only used with $a_i<b_i$.
-- source:
--   Wikipedia, "Gauss's law for magnetism" (uploaded PDF, 5 pp.), p. 1, section 'Integral form' (flux through a closed surface S, outward normal; the surface of a cube is listed as an example of a closed surface on p. 2); Wikipedia, "Maxwell's equations" (uploaded PDF, 24 pp.), p. 7, section 'Flux and divergence'.

import Definitions.Def_TongEM_wave_ops

/-!
# Outward flux of a vector field through the boundary of a box

Support file for the mission on Gauss's law for magnetism (Wikipedia,
"Gauss's law for magnetism", section "Integral form"; Wikipedia, "Maxwell's
equations", section "Flux and divergence").

Space is `Larmor.Vec = EuclideanSpace ℝ (Fin 3)`; the divergence `Larmor.divg`
and curl `Larmor.curl` come from `Def_Larmor_vec3`, and the gradient
`TongEM.grad` and smoothness predicate `TongEM.SmoothV` from
`Def_TongEM_wave_ops`.  This file adds the closed surfaces used for the integral
form of the law: boundaries of axis-parallel boxes.
-/

namespace GaussMagnetism

open Larmor

/-- The outward flux `∯_{∂Ω} F · dS` of a vector field `F` through the boundary of
the axis-parallel box `Ω = [a₀, b₀] × [a₁, b₁] × [a₂, b₂]`.  The boundary consists
of six rectangular faces; on the face `xᵢ = bᵢ` the outward unit normal is `+eᵢ`
and on the face `xᵢ = aᵢ` it is `-eᵢ`, so the flux through that pair of faces is
the integral over the face of `Fᵢ(…, bᵢ, …) - Fᵢ(…, aᵢ, …)`.  The value is only
meaningful when `aᵢ < bᵢ` for every `i`. -/
noncomputable def boxFlux (F : Vec → Vec) (a b : Vec) : ℝ :=
  (∫ y in a 1..b 1, ∫ z in a 2..b 2, (F !₂[b 0, y, z] 0 - F !₂[a 0, y, z] 0)) +
  (∫ x in a 0..b 0, ∫ z in a 2..b 2, (F !₂[x, b 1, z] 1 - F !₂[x, a 1, z] 1)) +
  (∫ x in a 0..b 0, ∫ y in a 1..b 1, (F !₂[x, y, b 2] 2 - F !₂[x, y, a 2] 2))

end GaussMagnetism


