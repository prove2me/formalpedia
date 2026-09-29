-- Prove2me | Definitions.Def_MathematicsOfWater_PipeFlow
-- name    : MathematicsOfWater_PipeFlow
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T15:32:00.148679+00:00
-- url     : https://prove2.me/theorems/6319f421-3960-4acc-bf27-133500c77d4b
-- title:
--   Hagen–Poiseuille pipe flow: radial equation, boundary conditions, profile, flow rate
-- statement:
--   Definitions for steady, axially symmetric, pressure-driven flow of a Newtonian fluid in a straight cylindrical pipe (Lecture 15, slides 13–16). Parameters: viscosity $\eta$, pipe length $L$, pressure drop $\Delta p=p(0)-p(L)$, pipe diameter $d$; the velocity is axial, $\mathbf v=v(r)\,\mathbf e_z$, depending only on the distance $r$ to the axis.
--
--   1. **Radial equation** `SatisfiesRadialStokesODE η L Δp R v`: for every $0<r<R$, $v$ and $r\mapsto r v'(r)$ are differentiable at $r$ and
--   $$\frac1r\frac{d}{dr}\Big(r\frac{dv}{dr}\Big)=-\frac{\Delta p}{\eta L}.$$
--   2. **Pipe flow** `IsPipeFlow η L Δp d v`: $v$ satisfies the radial equation on $(0,d/2)$, is bounded on $(0,d/2)$ ("$v(r=0)<\infty$"), is continuous at the wall $r=d/2$ from inside, and $v(d/2)=0$ (no slip).
--   3. **Poiseuille profile** `poiseuilleProfile η L Δp d`: $v_P(r)=\frac{\Delta p}{4\eta L}\big(\frac{d^2}{4}-r^2\big)$.
--   4. **Flow rate** `flowRate d v`: $Q=\int_0^{d/2}v(r)\,2\pi r\,dr$.
--   5. **Average velocity** `averageVelocity d v`: $\langle v\rangle=Q/(\pi d^2/4)$.
--
--   **Formalization Note** The radial equation is the form obtained on slide 15 after integrating the momentum balance along the pipe; the pressure field itself is not modelled.
-- source:
--   Lecture 15: The Mathematics of Water, PHYS 461 & 561 (Biophysics), Drexel University, Fall 2011-2012, 11/15/2011, lecturer Luis Cruz (for Brigita Urbanc), www.physics.drexel.edu/~brigita/COURSES/BIOPHYS_2011-2012/, slides 13–16

import Mathlib

namespace MathematicsOfWater

open Real

/-- The steady radial momentum balance for axial flow `v(r)` in a cylindrical pipe
(Lecture 15, slides 14–15):
`(1/r) d/dr (r dv/dr) = -Δp / (η L)` at every radius `0 < r < R`,
together with the differentiability needed for the two derivatives to exist. -/
def SatisfiesRadialStokesODE (η L Δp R : ℝ) (v : ℝ → ℝ) : Prop :=
  ∀ r ∈ Set.Ioo 0 R,
    DifferentiableAt ℝ v r ∧
    DifferentiableAt ℝ (fun s => s * deriv v s) r ∧
    (1 / r) * deriv (fun s => s * deriv v s) r = -(Δp / (η * L))

/-- Steady pressure-driven (Hagen–Poiseuille) flow in a pipe of diameter `d`, length `L`,
viscosity `η` and pressure drop `Δp = p(0) - p(L)` (Lecture 15, slides 13–16):
the velocity `v(r)` satisfies the radial equation on `0 < r < d/2`, stays finite
(bounded) near the axis, and obeys the no-slip condition `v(d/2) = 0` at the wall,
with `v` continuous at the wall from inside. -/
def IsPipeFlow (η L Δp d : ℝ) (v : ℝ → ℝ) : Prop :=
  SatisfiesRadialStokesODE η L Δp (d / 2) v ∧
  (∃ M : ℝ, ∀ r ∈ Set.Ioo 0 (d / 2), |v r| ≤ M) ∧
  ContinuousWithinAt v (Set.Iio (d / 2)) (d / 2) ∧
  v (d / 2) = 0

/-- The parabolic Poiseuille velocity profile
`v(r) = Δp / (4 η L) * (d²/4 - r²)` (Lecture 15, slide 16). -/
noncomputable def poiseuilleProfile (η L Δp d : ℝ) (r : ℝ) : ℝ :=
  Δp / (4 * η * L) * (d ^ 2 / 4 - r ^ 2)

/-- Volumetric flow rate through the circular cross-section of diameter `d`:
`Q = ∫₀^{d/2} v(r) · 2πr dr` (Lecture 15, slide 16). -/
noncomputable def flowRate (d : ℝ) (v : ℝ → ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..(d / 2), v r * (2 * π * r)

/-- Average velocity `⟨v⟩ = Q / (π d² / 4)` over the cross-section (Lecture 15, slide 16). -/
noncomputable def averageVelocity (d : ℝ) (v : ℝ → ℝ) : ℝ :=
  flowRate d v / (π * d ^ 2 / 4)

end MathematicsOfWater


