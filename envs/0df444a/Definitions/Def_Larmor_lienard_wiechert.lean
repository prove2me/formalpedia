-- Prove2me | Definitions.Def_Larmor_lienard_wiechert
-- name    : Larmor_lienard_wiechert
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T01:03:42.443625+00:00
-- url     : https://prove2.me/theorems/7249157e-6a06-4181-b12f-cf15474bebc1
-- title:
--   Retarded time and the Liénard–Wiechert fields of a point charge
-- statement:
--   This file introduces the retarded-time relation and the exact solution of Maxwell's equations produced by a point charge in arbitrary motion.
--
--   A point charge $q$ moves along a worldline $w:\mathbb{R}\to\mathbb{R}^3$. A time $t_r$ is a **retarded time** for the observation event $(t,x)$ when the light signal emitted from the charge's position $w(t_r)$ at time $t_r$ arrives at the observation point $x$ at time $t$:
--
--   $$t_r\le t\qquad\text{and}\qquad c\,(t-t_r)=\|x-w(t_r)\| .$$
--
--   Given such a $t_r$, write
--   $$R=\|x-w(t_r)\|,\qquad n=\frac{x-w(t_r)}{R},\qquad \beta=\frac{\dot w(t_r)}{c},\qquad a=\ddot w(t_r),\qquad \kappa=1-\langle n,\beta\rangle .$$
--   The **Liénard–Wiechert fields** are
--
--   $$E=\frac{q}{4\pi\varepsilon_0}\left[\frac{1-\|\beta\|^2}{\kappa^3R^2}\,(n-\beta)
--   +\frac{1}{c^2\kappa^3R}\;n\times\bigl((n-\beta)\times a\bigr)\right],
--   \qquad B=\frac{1}{c}\,n\times E .$$
--
--   The first bracketed term is the velocity (or "Coulomb") field, falling off like $R^{-2}$ and reducing to the Coulomb field of a charge at rest; the second is the acceleration (or radiation) field, falling off like $R^{-1}$, transverse to $n$, and responsible for all radiated energy. These expressions are the exact retarded solution of Maxwell's equations for a point source and are the input to every computation in this mission.
--
--   **Formalization Note** The retarded time enters as an explicit argument rather than being constructed: a statement that needs "the" retarded time supplies a time, or a function of the observation event, satisfying the relation above, and uniqueness is a separate theorem of this mission. The velocity $\dot w$ and acceleration $\ddot w$ are iterated derivatives of the worldline; where they do not exist, the ambient convention supplies the value $0$.
-- source:
--   https://en.wikipedia.org/wiki/Larmor_formula — Derivation section: "The electric and magnetic fields are given by the Liénard–Wiechert field equations ... The variables are all evaluated at the retarded time $t_r = t - R/c$"; J. D. Jackson, Classical Electrodynamics, 3rd ed., Wiley 1998, eq. (14.14).

import Definitions.Def_Larmor_vec3

namespace Larmor

/-- `tr` is a retarded time for the observation event `(t, x)` relative to the worldline
`w` of a point charge: the light signal emitted from `w tr` at time `tr` reaches `x` at
time `t`. -/
def IsRetardedTime (c : ℝ) (w : ℝ → Vec) (t : ℝ) (x : Vec) (tr : ℝ) : Prop :=
  tr ≤ t ∧ c * (t - tr) = ‖x - w tr‖

/-- The Liénard-Wiechert electric field at the observation point `x` produced by a point
charge `q` moving along the worldline `w`, expressed through the retarded time `tr`.
With `Rv = x - w tr`, `R = ‖Rv‖`, `n = Rv / R`, `β = w' tr / c`, `a = w'' tr` and
`κ = 1 - ⟪n, β⟫`, this is
`E = q / (4 π ε₀) * ((1 - ‖β‖²) / (κ³ R²) * (n - β) + 1 / (c² κ³ R) * n × ((n - β) × a))`. -/
noncomputable def lwE (q ε₀ c : ℝ) (w : ℝ → Vec) (tr : ℝ) (x : Vec) : Vec :=
  let R := ‖x - w tr‖
  let n := R⁻¹ • (x - w tr)
  let b := c⁻¹ • deriv w tr
  let a := deriv (deriv w) tr
  let k := 1 - inner ℝ n b
  (q / (4 * Real.pi * ε₀)) •
    (((1 - ‖b‖ ^ 2) / (k ^ 3 * R ^ 2)) • (n - b)
      + (1 / (c ^ 2 * k ^ 3 * R)) • cross n (cross (n - b) a))

/-- The Liénard-Wiechert magnetic field, `B = n × E / c` with `n` the unit vector from the
retarded position of the charge to the observation point. -/
noncomputable def lwB (q ε₀ c : ℝ) (w : ℝ → Vec) (tr : ℝ) (x : Vec) : Vec :=
  c⁻¹ • cross (‖x - w tr‖⁻¹ • (x - w tr)) (lwE q ε₀ c w tr x)

end Larmor


