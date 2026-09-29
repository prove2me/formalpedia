-- Prove2me | Definitions.Def_DynamicsRelativity_CentralForces_Defs
-- name    : DynamicsRelativity_CentralForces_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-22T23:15:07.536698+00:00
-- url     : https://prove2.me/theorems/4f8d5c77-05fa-49f1-a87a-47bbe04b99a4
-- title:
--   Central force motion, the Kepler problem, and ellipses with a focus at the origin
-- statement:
--   This bundle sets up the objects of Tong §4 (Central Forces), and is imported by every theorem of the mission.
--
--   **The arena.** A point particle moves in Euclidean $3$-space, written $\mathrm{Vec}$, with its standard inner product $\langle\cdot,\cdot\rangle$ and norm $\lVert\cdot\rVert$. A trajectory is a map $x:\mathbb R\to\mathrm{Vec}$; its velocity $\dot x$ and acceleration $\ddot x$ are the first and second pointwise derivatives, and $\mathrm{cross}(a,b)$ is the usual cross product $a\times b$.
--
--   **Central force motion.** Following Tong's equation (4.1), a particle of mass $m$ moves in a central force field with radial profile $F$ when
--
--   $$ m\,\ddot x(t) \;=\; F\big(r(t)\big)\,\frac{x(t)}{r(t)}, \qquad r(t)=\lVert x(t)\rVert , $$
--
--   together with the standing conventions of the chapter: the mass is positive, the trajectory is twice continuously differentiable on all of $\mathbb R$, and it never meets the origin, where a central field is singular. For a force derived from a central potential $V$ one has $F=-dV/dr$.
--
--   **The Kepler problem.** The inverse-square case is $F(r)=-km/r^{2}$, the force of Tong's potential (4.12) $V(r)=-km/r$, with $k=GM$ for gravitational attraction. Unfolded, a Kepler motion satisfies $m\ddot x = -km\,x/r^{3}$.
--
--   **Conserved quantities.** The angular momentum is the vector $L(t)=m\,x(t)\times\dot x(t)$, and the total energy of the Kepler problem is
--
--   $$ E(t) \;=\; \tfrac12 m\lVert\dot x(t)\rVert^{2} \;-\; \frac{km}{r(t)} . $$
--
--   **Swept area.** The area swept by the radius vector between two times is $\tfrac12\int\lVert x\times\dot x\rVert\,dt$, the invariant form of the element $\delta A=\tfrac12 r^{2}\delta\theta$ used in Tong §4.3.2.
--
--   **Ellipse with a focus at the origin.** A set $S$ qualifies when there are a nonzero normal $n$, a second focus $c$ with $\langle n,c\rangle=0$, and a number $a$ with $\lVert c\rVert<2a$, such that $S$ is exactly the set of points $y$ of the plane $\langle n,y\rangle=0$ with
--
--   $$ \lVert y\rVert + \lVert y-c\rVert \;=\; 2a . $$
--
--   This is the two-foci ("string") characterization, with the origin as one of the two foci; the inequality $\lVert c\rVert<2a$ forces $a>0$ and rules out the degenerate loci, while $c=0$ gives a circle.
--
--   These definitions are the shared vocabulary of the whole series on the source notes: they are stated for a general central force wherever the source's result is general, and specialized to the inverse-square law only where it is needed.
--
--   **Formalization Note.** The arena is `EuclideanSpace ℝ (Fin 3)`. Smoothness is `ContDiff ℝ 2` and derivatives are Mathlib's `deriv`. The force enters through its radial profile $F$ rather than through a potential, so no derivative of a potential is evaluated at a point where it may fail to exist.
-- source:
--   David Tong, Dynamics and Relativity, University of Cambridge Part IA Mathematical Tripos lecture notes, Lent 2013, http://www.damtp.cam.ac.uk/user/tong/relativity.html — §4 Central Forces, pp. 48–62; eq. (4.1) p. 48, eq. (4.5) p. 50, eq. (4.12) p. 56, and the area element of §4.3.2 p. 61.

import Mathlib

namespace DynamicsRelativity

/-- Euclidean 3-space: the arena in which a point particle moves. -/
abbrev Vec : Type := EuclideanSpace ℝ (Fin 3)

/-- The cross product `a × b` of two vectors of Euclidean 3-space. -/
noncomputable def cross (a b : Vec) : Vec :=
  WithLp.toLp 2 (crossProduct a.ofLp b.ofLp)

/-- The velocity `ẋ` of a trajectory `x : ℝ → Vec`. -/
noncomputable def vel (x : ℝ → Vec) : ℝ → Vec := deriv x

/-- The acceleration `ẍ` of a trajectory `x : ℝ → Vec`. -/
noncomputable def acc (x : ℝ → Vec) : ℝ → Vec := deriv (deriv x)

/-- `CentralForceMotion m F x` says that `x : ℝ → Vec` is the trajectory of a point
particle of mass `m > 0` moving in a central force field whose radial component at
distance `r` from the origin is `F r`; that is, Tong eq. (4.1),
`m ẍ = F(r) r̂`, where `r = ‖x‖` and `r̂ = x / ‖x‖`.
For a force derived from a central potential `V(r)` one has `F = -dV/dr`.
The trajectory is assumed twice continuously differentiable and to avoid the
origin, where a central force field is generally singular. -/
structure CentralForceMotion (m : ℝ) (F : ℝ → ℝ) (x : ℝ → Vec) : Prop where
  /-- The particle has positive mass. -/
  mass_pos : 0 < m
  /-- The trajectory is twice continuously differentiable. -/
  smooth : ContDiff ℝ 2 x
  /-- The particle never reaches the centre of attraction. -/
  ne_origin : ∀ t, x t ≠ 0
  /-- Newton's second law for a central force. -/
  eom : ∀ t, m • acc x t = (F ‖x t‖ / ‖x t‖) • x t

/-- The radial force of the inverse-square (Kepler/Coulomb) law for a particle of
mass `m`: `F(r) = -k m / r²`, the force derived from Tong's potential (4.12)
`V(r) = -k m / r`. Here `k = GM` for gravity; `k > 0` is the attractive case. -/
noncomputable def keplerForce (k m : ℝ) (r : ℝ) : ℝ := -(k * m) / r ^ 2

/-- `KeplerMotion k m x`: the trajectory of a particle of mass `m` in the
inverse-square central field of strength `k` (Tong §4.3.1, the Kepler problem). -/
def KeplerMotion (k m : ℝ) (x : ℝ → Vec) : Prop :=
  CentralForceMotion m (keplerForce k m) x

/-- The angular momentum `L = m x × ẋ` of a particle of mass `m` (Tong §4, p. 48). -/
noncomputable def angularMomentum (m : ℝ) (x : ℝ → Vec) (t : ℝ) : Vec :=
  m • cross (x t) (vel x t)

/-- The total energy `E = ½ m ‖ẋ‖² - k m / r` of a particle of mass `m` in the
inverse-square field of strength `k` (Tong §4.3.1, using the potential (4.12)). -/
noncomputable def keplerEnergy (k m : ℝ) (x : ℝ → Vec) (t : ℝ) : ℝ :=
  (1 / 2) * m * ‖vel x t‖ ^ 2 - k * m / ‖x t‖

/-- The area swept out by the radius vector between times `t₀` and `t₁`
(Tong §4.3.2, `δA = ½ r² δθ`): for planar motion the element of area swept by the
segment joining the origin to the particle is `½ ‖x × ẋ‖ dt`. -/
noncomputable def sweptArea (x : ℝ → Vec) (t₀ t₁ : ℝ) : ℝ :=
  (1 / 2) * ∫ t in t₀..t₁, ‖cross (x t) (vel x t)‖

/-- `IsEllipseWithFocusAtOrigin S` says that `S` is a (possibly circular)
nondegenerate ellipse lying in a plane through the origin, having the origin as one
of its two foci. Concretely: there are a nonzero normal vector `n`, a second focus
`c` lying in the plane `n ᗮ` through the origin, and a real number `a` with
`‖c‖ < 2a`, such that `S` consists of exactly those points `y` of that plane whose
distances to the two foci `0` and `c` sum to `2a`. -/
def IsEllipseWithFocusAtOrigin (S : Set Vec) : Prop :=
  ∃ (n c : Vec) (a : ℝ), n ≠ 0 ∧ inner ℝ n c = 0 ∧ ‖c‖ < 2 * a ∧
    S = {y : Vec | inner ℝ n y = 0 ∧ ‖y‖ + ‖y - c‖ = 2 * a}

end DynamicsRelativity


