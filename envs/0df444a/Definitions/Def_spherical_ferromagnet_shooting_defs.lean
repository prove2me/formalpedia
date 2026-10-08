-- Prove2me | Definitions.Def_spherical_ferromagnet_shooting_defs
-- name    : spherical_ferromagnet_shooting_defs
-- status  : Definition
-- author  : @shivm
-- created : 2026-10-04T18:18:01.471091+00:00
-- url     : https://prove2.me/theorems/902a4987-18cf-4c21-8048-cac3a09168d4
-- title:
--   Shooting solutions and pole regularity for the $\kappa=4$ profile equation
-- statement:
--   Two predicates used in the shooting argument for the profile equation (2.6) at $\kappa=4$:
--
--   $$h''+\cot\theta\,h'-\frac{\sin 2h}{2\sin^2\theta}-\frac{\kappa}{2}\sin(2h-2\theta)=0.$$
--
--   1. $\mathrm{ShootSol}(a,h)$: $h$ is $C^\infty$ on $[0,\pi/2]$, $h(0)=0$, $h'(0)=a$, and $h$ solves (2.6) with $\kappa=4$ on $(0,\pi/2)$.
--   2. $\mathrm{PoleRep}(h)$: for some $\delta\in(0,\pi/2)$ there are $A_1,B_1$, $C^\infty$ on $[\cos\delta,1]$, with
--   $$\cos h(\theta)=A_1(\cos\theta),\qquad \sin h(\theta)=B_1(\cos\theta)\,\sin\theta\qquad(0\le\theta\le\delta).$$
--
--   $\mathrm{PoleRep}$ is regularity at the north pole: it makes the field $(\sin h\cos\varphi,\sin h\sin\varphi,\cos h)$ smooth there. Smoothness of $h$ in $\theta$ alone does not.
--
--   **Formalization Note** $h'(0)$ is the one-sided derivative `derivWithin h (Icc 0 (π/2)) 0`.
-- source:
--   S. Gustafson, D. Meinert, C. Melcher, Saddle Point Configurations for Spherical Ferromagnets, arXiv:2509.05159v2, https://arxiv.org/abs/2509.05159, eq. (2.6), Definition 3.1; AIM open problems list, problem 241

import Definitions.Def_spherical_ferromagnet_profile_defs

namespace SphericalFerromagnet

open Real Set
open scoped ContDiff

/-- `h` is a shot with slope `a` for the profile equation (2.6) at `κ = 4`: smooth on
`[0, π/2]`, `h(0) = 0`, `h'(0) = a`, solving (2.6) on `(0, π/2)`. -/
def ShootSol (a : ℝ) (h : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ h (Icc 0 (π / 2)) ∧ h 0 = 0 ∧ derivWithin h (Icc 0 (π / 2)) 0 = a ∧
    ∀ θ ∈ Ioo (0 : ℝ) (π / 2), profileOperator 4 h θ = 0

/-- Regularity at the north pole: near `θ = 0`, `cos h(θ) = A₁(cos θ)` and
`sin h(θ) = B₁(cos θ) sin θ` with `A₁, B₁` smooth on `[cos δ, 1]`. -/
def PoleRep (h : ℝ → ℝ) : Prop :=
  ∃ δ ∈ Ioo (0 : ℝ) (π / 2), ∃ A₁ B₁ : ℝ → ℝ,
    ContDiffOn ℝ ∞ A₁ (Icc (Real.cos δ) 1) ∧ ContDiffOn ℝ ∞ B₁ (Icc (Real.cos δ) 1) ∧
    ∀ θ ∈ Icc (0 : ℝ) δ,
      Real.cos (h θ) = A₁ (Real.cos θ) ∧ Real.sin (h θ) = B₁ (Real.cos θ) * Real.sin θ

end SphericalFerromagnet


