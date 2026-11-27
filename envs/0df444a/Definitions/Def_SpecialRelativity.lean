-- Prove2me | Definitions.Def_SpecialRelativity
-- name    : SpecialRelativity
-- status  : Definition
-- author  : @LG
-- created : 2026-11-27T01:48:13.564112+00:00
-- url     : https://prove2.me/theorems/b624b915-b142-4bd8-bd83-4495154c4454
-- title:
--   Special relativity: Minkowski space, Lorentz transformations and four-momentum
-- statement:
--   This definition file introduces, in the namespace `SpecialRelativity`, the notions used to formalize the mathematical skeleton of special relativity on plain spacetime quadruples, in natural units ($c = 1$) with metric signature $(-,+,+,+)$.
--
--   **1. Spacetime.** `Sp = Fin 4 → ℝ` — event quadruples $(ct, x, y, z)$ in standard coordinates with $c = 1$, a plain Mathlib Pi type; no manifold machinery. `minkDiag` is the signature diagonal $(-1, 1, 1, 1)$ and `etaM = Matrix.diagonal minkDiag` is the Minkowski metric matrix.
--
--   **2. The interval (`mink`) and its causal classification (`IsNull`, `IsTimelike`).** The Minkowski bilinear form — the invariant "interval" of the source, the time coordinate entering with a minus sign:
--
--   $$\eta(u, v) \;=\; -u_0 v_0 + u_1 v_1 + u_2 v_2 + u_3 v_3.$$
--
--   `IsNull u` is $\eta(u,u) = 0$ — null (lightlike) separation, the class of separations realized by light signals; `IsTimelike u` is $\eta(u,u) < 0$ — timelike separation, the class of separations connectable by massive bodies.
--
--   **3. Lorentz transformations (`IsLorentz`).** A $4\times 4$ real matrix `A` is a Lorentz transformation when it preserves the Minkowski form exactly:
--
--   $$A^{T}\,\eta\,A \;=\; \eta,$$
--
--   i.e. the interval between two events has the same value in the transformed coordinates — the geometric content of the source's "the interval between two events has the same value for all observers independent of their relative velocity".
--
--   **4. Inertial motion (`IsInertial`).** A worldline $\gamma : \mathbb{R} \to Sp$ is inertial when it is straight with constant velocity: $\exists\, a\, v,\ \forall\, t,\ \gamma(t) = a + t\,v$ — motion in a frame "with no acceleration".
--
--   **5. Velocity, Lorentz factor, boost (`spatialSpeed`, `gammaFactor`, `boost`).** For a velocity vector in coordinate-time parametrization ($v_0 = 1$), `spatialSpeed v` is the Euclidean norm $s = \sqrt{v_1^2 + v_2^2 + v_3^2}$ of the spatial components, and `gammaFactor s` is the Lorentz factor $\gamma(s) = 1/\sqrt{1 - s^2}$. The standard Lorentz boost along the $x$-axis with velocity $\beta$ is defined entrywise as the matrix of
--
--   $$t' = \gamma(t - \beta x), \qquad x' = \gamma(x - \beta t), \qquad y' = y, \qquad z' = z,$$
--
--   i.e. $\gamma$ on the $(t,t)$ and $(x,x)$ entries, $-\beta\gamma$ on the off-diagonal $(t,x)$ and $(x,t)$ entries, $1$ on the remaining diagonal and $0$ elsewhere. For $|\beta| < 1$ it is a Lorentz transformation (proved as part of the simultaneity milestone).
--
--   **6. Four-momentum (`fourMomentum`).** For a particle of rest mass `m` moving with velocity `v` ($v_0 = 1$, spatial speed $s < 1$), the four-momentum is
--
--   $$P = m\,\gamma\,(1, v_1, v_2, v_3), \qquad \gamma = 1/\sqrt{1 - s^2}:$$
--
--   time component the energy $E = m\gamma$ (units $c = 1$), spatial components the momentum $p = m\gamma\,v$ — "the energy and momentum … form a four-vector in relativity".
--
--   **7. Proper time (`properTime`).** Along a worldline $\gamma$ between parameter values $t_1, t_2$, the integral
--
--   $$\Delta\tau \;=\; \int_{t_1}^{t_2} \sqrt{-\eta(\gamma'(t), \gamma'(t))}\;dt,$$
--
--   the time actually elapsed on a clock carried by the worldline (real, since for a physical worldline the integrand's argument is $\ge 0$).
--
--   **Formalization note.** All statements live on the plain coordinate space `Fin 4 → ℝ` with Mathlib's `Matrix`/`mulVec` for the linear algebra and Mathlib's `deriv`/`∫` for proper time; natural units $c=1$ and signature $(-,+,+,+)$ throughout. The dynamical derivations of the source (Einstein's 1905 argument for $E = mc^2$), electrodynamics, the velocity-addition formula and length contraction are out of scope, as documented in the mission description.
-- source:
--   Wikipedia, Special relativity, https://en.wikipedia.org/wiki/Special_relativity (source of the quoted statements, reproduced verbatim in the definition file)

import Mathlib

/-!
Special relativity — the mathematical skeleton of the source article, formalized
in a concrete Minkowski framework.

Source: Wikipedia, *Special relativity*,
https://en.wikipedia.org/wiki/Special_relativity .  Exact source statements:

"In physics, the special theory of relativity, or simply special relativity, is
a scientific theory of the relationship between space and time. In Albert
Einstein's 1905 paper, 'On the Electrodynamics of Moving Bodies', the theory is
presented as being based on just two postulates:

The laws of physics are invariant (identical) in all inertial frames of
reference (that is, frames of reference with no acceleration). This is known as
the principle of relativity.

The speed of light in vacuum is the same for all observers, regardless of the
motion of light source or observer. This is known as the principle of light
constancy, or the principle of light speed invariance."

Consequences listed by the source: "The relativity of simultaneity - events that
appear simultaneous to one observer may not be simultaneous to an observer in
motion"; "Time dilation - time measured between two events by observers in
motion differ"; the Lorentz transformation of velocities; and "Combined with
other laws of physics, the two postulates of special relativity predict the
equivalence of mass and energy, as expressed in the mass-energy equivalence
formula E=mc2, where c is the speed of light in vacuum."  On the geometry: "A
defining feature of special relativity is the replacement of Euclidean geometry
with Lorentzian geometry. Distances in Euclidean geometry are calculated with
the Pythagorean theorem and only involved spatial coordinates. In Lorentzian
geometry, 'distances' become 'intervals' and include a time coordinate with a
minus sign. Unlike spatial distances, the interval between two events has the
same value for all observers independent of their relative velocity. When
comparing two sets of coordinates in relative motion the Lorentz transformation
replaces the Galilean transformation of Newtonian mechanics."  On mass-energy:
"The energy and momentum, which are separate in Newtonian mechanics, form a
four-vector in relativity, and this relates the time component (the energy) to
the space components (the momentum) in a non-trivial way."  Einstein combined
the two postulates into the Lorentz transformation: "The universal principle of
the special theory of relativity is contained in the postulate: The laws of
physics are invariant with respect to Lorentz transformations."

Scope, disclosed.  Natural units are used throughout: the speed of light is
`c = 1`, spacetime is `Fin 4 -> R` in standard coordinates `(ct, x, y, z)`, and
the Minkowski form has signature `(-,+,+,+)`.  The mission formalizes the
mathematical skeleton of the source: the Minkowski interval and its causal
classification, Lorentz transformations as the exact preservation of the
interval, the standard boost along the x-axis, the four-momentum, and proper
time along a worldline; the theorems are the source's core consequences in
their precise form — invariance of the light cone (light speed invariance),
the Lorentz group, time dilation, the relativity of simultaneity, and the
energy-momentum relation `P . P = -m^2` (equivalently `E^2 - |p|^2 = m^2`),
the content of mass-energy equivalence `E = mc^2` in units `c = 1`.  What is
NOT formalized: the dynamical derivations of the source (Einstein's 1905
argument for `E = mc^2` from conservation laws), electrodynamics, the velocity-
addition formula, and length contraction (which needs a simultaneity convention
for the measurement of moving rods; it is reachable from the present framework
but is left out to keep the mission focused).
-/

namespace SpecialRelativity

open Matrix

/-- Spacetime: event quadruples `(ct, x, y, z)` in natural units, `c = 1`. -/
abbrev Sp := Fin 4 → ℝ

/-- The Minkowski signature diagonal `(-1, 1, 1, 1)`. -/
def minkDiag : Fin 4 → ℝ := fun i => if i = 0 then -1 else 1

/-- The Minkowski metric matrix of signature `(-,+,+,+)`. -/
def etaM : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal minkDiag

/-- The Minkowski bilinear form — the invariant interval of the source, with
the time coordinate entering with a minus sign:

`η(u, v) = -u₀ v₀ + u₁ v₁ + u₂ v₂ + u₃ v₃`. -/
def mink (u v : Sp) : ℝ := -u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3

/-- Null (lightlike) separation: `Δs² = 0` — the separation class of events
connected by light signals. -/
def IsNull (u : Sp) : Prop := mink u u = 0

/-- Timelike separation: `Δs² < 0` in the `(-,+,+,+)` convention — the
separation class of events connectable by massive bodies. -/
def IsTimelike (u : Sp) : Prop := mink u u < 0

/-- A Lorentz transformation: a linear coordinate change that preserves the
Minkowski form exactly — "the interval between two events has the same value
for all observers independent of their relative velocity". -/
def IsLorentz (A : Matrix (Fin 4) (Fin 4) ℝ) : Prop := Aᵀ * etaM * A = etaM

/-- Inertial motion: a straight worldline with constant velocity, `γ t = a + t v`
— motion in a frame of reference "with no acceleration". -/
def IsInertial (γ : ℝ → Sp) : Prop := ∃ a v : Sp, ∀ t : ℝ, γ t = a + t • v

/-- The spatial speed of a velocity vector in coordinate-time parametrization
(`v 0 = 1`): the Euclidean norm of the spatial components. -/
noncomputable def spatialSpeed (v : Sp) : ℝ := Real.sqrt ((v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2)

/-- The Lorentz factor `γ(s) = 1 / √(1 - s²)` of the source. -/
noncomputable def gammaFactor (s : ℝ) : ℝ := 1 / Real.sqrt (1 - s ^ 2)

/-- The standard Lorentz boost along the `x`-axis with velocity `β`: in blocks,

`t' = γ(t - β x)`,  `x' = γ(x - β t)`,  `y' = y`,  `z' = z`,

as a matrix acting on event coordinates; `|β| < 1` makes it a Lorentz
transformation (part of the simultaneity milestone). -/
noncomputable def boost (β : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j =>
    if i = 0 ∧ j = 0 then gammaFactor β
    else if i = 0 ∧ j = 1 then -β * gammaFactor β
    else if i = 1 ∧ j = 0 then -β * gammaFactor β
    else if i = 1 ∧ j = 1 then gammaFactor β
    else if i = j then 1 else 0

/-- The four-momentum of a particle of rest mass `m` moving with velocity `v`
(in coordinate-time parametrization, `v 0 = 1`, spatial speed `< 1`):

`P = m γ (1, v₁, v₂, v₃)`, `γ = 1/√(1 - s²)`, `s` the spatial speed.

The time component is the energy `E = m γ` (in units `c = 1`), the spatial
components the momentum `p = m γ v` — "the energy and momentum ... form a
four-vector in relativity". -/
noncomputable def fourMomentum (m : ℝ) (v : Sp) : Sp := fun i =>
  if i = 0 then m * gammaFactor (spatialSpeed v)
  else m * (v i) * gammaFactor (spatialSpeed v)

/-- Proper time along a worldline between parameter values `t₁, t₂`: the
integral of `√(-η(γ', γ'))` — the time actually elapsed on a clock carried by
the worldline.  For an inertial (straight) worldline this is the time component
of the motion itself. -/
noncomputable def properTime (γ : ℝ → Sp) (t₁ t₂ : ℝ) : ℝ :=
  ∫ t in t₁..t₂, Real.sqrt (-mink (deriv γ t) (deriv γ t))

end SpecialRelativity


