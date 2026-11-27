-- Prove2me | Definitions.Def_WorldLine
-- name    : WorldLine
-- status  : Definition
-- author  : @LG
-- created : 2026-11-27T02:09:57.255341+00:00
-- url     : https://prove2.me/theorems/04fdf496-0e95-5d7a-8247-29e4814d52c1
-- title:
--   World lines: timelike curves, proper time, four-velocity and geodesics in Minkowski spacetime
-- statement:
--   This definition file introduces, in the namespace `WorldLine`, the notions used to formalize the world line of an object — its path through 4-dimensional spacetime — on plain spacetime quadruples, in natural units ($c = 1$) with bilinear form of signature $(-,+,+,+)$.
--
--   **1. Spacetime and the bilinear form.** `Sp = Fin 4 → ℝ` — event quadruples $(ct, x, y, z)$ in standard coordinates, a plain Mathlib Pi type. `minkDiag` is the signature diagonal $(-1, 1, 1, 1)$, `etaM = Matrix.diagonal minkDiag`, and the Minkowski bilinear form — "the structure of spacetime is determined by a bilinear form $\eta$" — is
--
--   $$\eta(u, v) \;=\; -u_0 v_0 + u_1 v_1 + u_2 v_2 + u_3 v_3.$$
--
--   **2. Causal trichotomy (`IsNull`, `IsTimelike`, `IsSpacelike`).** `IsNull u`: $\eta(u,u) = 0$ — "light-like curves, having at each point the speed of light"; `IsTimelike u`: $\eta(u,u) < 0$ — "time-like curves, with a speed less than the speed of light", the tangents of worldlines; `IsSpacelike u`: $0 < \eta(u,u)$ — "space-like curves falling outside the light cone" (e.g. the length of a rod).
--
--   **3. Lorentz transformations (`IsLorentz`).** A $4\times 4$ real matrix `A` with $A^{T}\eta A = \eta$ — the changes between the inertial coordinate systems of the source.
--
--   **4. Four-velocity (`fourVelocity`).** For a timelike tangent $u$, the normalization to unit Minkowski norm:
--
--   $$\mathrm{fourVelocity}(u) \;=\; u \,/\, \sqrt{-\eta(u, u)},$$
--
--   componentwise; the tangent vector of the source "termed four-velocity", i.e. what the tangent becomes when proper time is the curve parameter.
--
--   **5. Worldlines (`IsWorldline`).** $\gamma : \mathbb{R} \to Sp$ is a worldline when it is continuously differentiable and its tangent is timelike or null at each point:
--
--   $$\mathrm{ContDiff}\ \mathbb{R}\ 1\ \gamma \;\wedge\; \forall\, t,\ \eta(\gamma'(t), \gamma'(t)) \le 0,$$
--
--   "a world line is either a time-like or a null curve in spacetime". Time orientation (Harvey's "future timelike") is deliberately not encoded.
--
--   **6. Proper time (`properTime`).** The arclength of the worldline in the Minkowski form between parameter values $t_1, t_2$:
--
--   $$\Delta\tau \;=\; \int_{t_1}^{t_2} \sqrt{-\eta(\gamma'(t), \gamma'(t))}\;dt,$$
--
--   "The length of M is called the proper time of the particle" (Harvey, quoted in the source).
--
--   **7. Free fall / geodesics (`IsGeodesic`).** $\gamma$ is a geodesic when it is twice continuously differentiable with vanishing coordinate acceleration at every parameter value, $\gamma''(t) = 0$ — the geodesic equation of flat Minkowski space in inertial coordinates, where the Christoffel symbols vanish. "World lines of freely falling particles/objects are called geodesics."
--
--   **Formalization note.** All statements live on the plain coordinate space `Fin 4 → ℝ` with Mathlib's `Matrix`/`mulVec` for the linear algebra and `deriv`/`∫` for proper time. No manifold machinery: curved-spacetime general relativity (nonvanishing Christoffel symbols), time orientation, world sheets/tubes and the QFT worldline formulation are out of scope, as documented in the mission description.
-- source:
--   Wikipedia, World line, https://en.wikipedia.org/wiki/World_line (source of the quoted statements, reproduced verbatim in the definition file)

import Mathlib

/-!
World lines — the path of an object through spacetime, formalized as curves in
a concrete Minkowski framework.

Source: Wikipedia, *World line*, https://en.wikipedia.org/wiki/World_line .
Exact source statements:

"The world line (or worldline) of an object is the path that an object traces
in 4-dimensional spacetime."  "A world line of an object (generally
approximated as a point in space, e.g., a particle or observer) is the sequence
of spacetime events corresponding to the history of the object. A world line is
a special type of curve in spacetime. ... A world line is either a time-like or
a null curve in spacetime."  On proper time (quoting F.R. Harvey): "A curve M
in [spacetime] is called a worldline of a particle if its tangent is future
timelike at each point. The arclength parameter is called proper time and
usually denoted tau. The length of M is called the proper time of the particle.
If the worldline M is a line segment, then the particle is said to be in free
fall."  On four-velocity: the tangent vector obtained as the limit of
"difference divided by Delta tau" "is associated with the normal 3-dimensional
velocity of the object (but it is not the same) and therefore termed
four-velocity"; "One usually uses the proper time of an object or an observer
as the curve parameter tau along the world line."  On special relativity: "The
structure of spacetime is determined by a bilinear form eta, which gives a real
number for each pair of events."  Curve types: "light-like curves, having at
each point the speed of light"; "time-like curves, with a speed less than the
speed of light"; "space-like curves falling outside the light cone."  On free
fall: "World lines of freely falling particles/objects are called geodesics. In
special relativity these are straight lines in Minkowski space."  On frames:
"Although the light cones are the same for all observers at a given spacetime
event, different observers ... have different simultaneous hyperplanes."

Scope, disclosed.  Natural units are used throughout: the speed of light is
`c = 1`, spacetime is `Fin 4 -> R` in standard coordinates `(ct, x, y, z)`, and
the bilinear form has signature `(-,+,+,+)`.  The mission formalizes the
mathematical skeleton of the source: worldlines as curves with timelike-or-null
tangent everywhere, the causal trichotomy (timelike / null / spacelike
separations), proper time as the arclength of a worldline, the four-velocity as
unit timelike tangent, and geodesics (free fall).  The theorems: invariance of
the causal classification under Lorentz transformations ("the light cones are
the same for all observers"), unit normalization of the four-velocity, the
proper time of a straight (inertial) worldline, frame-independence of proper
time, and the goal — geodesics of Minkowski space are straight lines in the
sense of the source ("If the worldline M is a line segment, then the particle
is said to be in free fall"): a twice-differentiable worldline whose coordinate
acceleration vanishes everywhere (the geodesic equation in inertial coordinates
of flat Minkowski space, where the Christoffel symbols vanish) is affine.

What is NOT formalized: general relativity (curved spacetime, Einstein field
equations, nonvanishing Christoffel symbols — no manifold machinery here), time
orientation (the "future timelike" half of Harvey's definition is dropped: the
theorems below do not distinguish future from past), world sheets and world
tubes (string theory), the worldline formulation of quantum field theory, and
the article's literary and historical material.
-/

namespace WorldLine

open Matrix

/-- Spacetime: event quadruples `(ct, x, y, z)` in natural units, `c = 1`. -/
abbrev Sp := Fin 4 → ℝ

/-- The Minkowski signature diagonal `(-1, 1, 1, 1)`. -/
def minkDiag : Fin 4 → ℝ := fun i => if i = 0 then -1 else 1

/-- The Minkowski metric matrix of signature `(-,+,+,+)`. -/
def etaM : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal minkDiag

/-- The Minkowski bilinear form `η` — "the structure of spacetime is determined
by a bilinear form", the time coordinate entering with a minus sign:
`η(u, v) = -u₀ v₀ + u₁ v₁ + u₂ v₂ + u₃ v₃`. -/
def mink (u v : Sp) : ℝ := -u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3

/-- Null (lightlike) separation: the class of light-like curves, "having at
each point the speed of light". -/
def IsNull (u : Sp) : Prop := mink u u = 0

/-- Timelike separation: the class of time-like curves, "with a speed less
than the speed of light" — the tangents of worldlines. -/
def IsTimelike (u : Sp) : Prop := mink u u < 0

/-- Spacelike separation: "space-like curves falling outside the light cone",
e.g. the length of a rod. -/
def IsSpacelike (u : Sp) : Prop := 0 < mink u u

/-- A Lorentz transformation: a linear change of inertial coordinates,
preserving the bilinear form exactly. -/
def IsLorentz (A : Matrix (Fin 4) (Fin 4) ℝ) : Prop := Aᵀ * etaM * A = etaM

/-- The four-velocity of a timelike tangent `u`: the tangent rescaled to unit
Minkowski norm — the tangent vector of the worldline "termed four-velocity",
when proper time is used as curve parameter. -/
noncomputable def fourVelocity (u : Sp) : Sp := fun i => u i / Real.sqrt (-(mink u u))

/-- A worldline: a continuously differentiable curve in spacetime whose
tangent is timelike or null at each point — "a world line is either a time-like
or a null curve in spacetime".  (Time orientation — Harvey's "future timelike"
— is not encoded.) -/
def IsWorldline (γ : ℝ → Sp) : Prop :=
  ContDiff ℝ 1 γ ∧ ∀ t : ℝ, mink (deriv γ t) (deriv γ t) ≤ 0

/-- Proper time along a worldline between parameter values `t₁, t₂`: the
arclength of the curve in the Minkowski form — "The arclength parameter is
called proper time ... The length of M is called the proper time of the
particle." -/
noncomputable def properTime (γ : ℝ → Sp) (t₁ t₂ : ℝ) : ℝ :=
  ∫ t in t₁..t₂, Real.sqrt (-mink (deriv γ t) (deriv γ t))

/-- A freely falling particle: a twice continuously differentiable worldline
with vanishing coordinate acceleration everywhere — the geodesic equation of
flat Minkowski space in inertial coordinates, where the Christoffel symbols
vanish.  "World lines of freely falling particles/objects are called geodesics.
In special relativity these are straight lines in Minkowski space." -/
def IsGeodesic (γ : ℝ → Sp) : Prop :=
  ContDiff ℝ 2 γ ∧ ∀ t : ℝ, deriv (deriv γ) t = 0

end WorldLine


