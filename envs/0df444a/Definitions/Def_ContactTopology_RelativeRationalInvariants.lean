-- Prove2me | Definitions.Def_ContactTopology_RelativeRationalInvariants
-- name    : ContactTopology_RelativeRationalInvariants
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-30T18:50:20.993888+00:00
-- url     : https://prove2.me/theorems/613777ad-6cd5-4985-abca-f3553132d9ce
-- title:
--   Relative signed quotient intersections and rational angular rotation
-- statement:
--   Let $D,\gamma:\mathbb R^2\to\mathbb R^4$ be lifts of an oriented disk and a parametrized circle in the antipodal quotient. Define their closed-disk intersection parameters by
--   $$I(D,\gamma)=\{v:|v|\le1,\ D(v)=\pm\gamma(u)\text{ for some }u\in S^1\}.$$
--   At a matching parameter, transport the circle tangent by the deck sign taking $\gamma(u)$ to $D(v)$. Evaluate the standard contact orientation on the ordered disk derivatives followed by that tangent, and take its integer sign. For finite $I$, sum these signs and divide by a positive boundary-covering multiplicity $r$ to obtain the relative normalized intersection count.
--
--   The implementation selects a matching circle parameter at each intersection. Applications must prove that all matching parameters give the same sign. No such independence or transversality is built into the definition.
--
--   For $f:\mathbb R\to S^1$, its winding predicate means that a continuous angular lift on $[0,2\pi]$ changes by $2\pi k$, where $k\in\mathbb Z$. The rational rotation predicate is
--   $$q=\frac{k}{r},\qquad r>0.$$
--   The direction of a nonzero complex coordinate vector is its normalization to the unit circle. The arbitrary assigned direction at zero is excluded by the nonvanishing hypotheses in applications.
--
--   These are relative geometric functionals and angular predicates. They do not assert invariance under changing the disk, push-off, trivialization or isotopy.
-- source:
--   Kenneth L. Baker and John B. Etnyre, Rational linking and contact geometry, corrected version, https://etnyre.math.gatech.edu/preprints/papers/ratlink.pdf, Section 1, pp. 2–3 (relative rational linking by normalized oriented intersection), and Section 1.2, pp. 4–5 (contact-framing push-off and winding divided by boundary multiplicity). The definitions here are concrete lifted relative quantities; general independence statements remain theorems to prove, not axioms of the definitions.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Rat.Cast.Defs

namespace ContactTopology.RationalInvariants
open BirkhoffGlobalSection Set
noncomputable section

/-- The contact orientation on the three-sphere, evaluated on three tangent vectors. -/
def contactVolume (y v w z : Phase) : ℝ :=
  2*(phaseRadialContact y v*phaseRadialContact w z-
    phaseRadialContact y w*phaseRadialContact v z+
    phaseRadialContact y z*phaseRadialContact v w)

/-- Integer-valued sign; non-transverse volume zero contributes zero. -/
def orientationSign (a : ℝ) : ℤ := if a < 0 then -1 else if 0 < a then 1 else 0

/-- Intersection parameters in the closed disk, with equality taken in the antipodal quotient. -/
def quotientIntersectionSet (D γ : Plane → Phase) : Set Plane :=
  {v | planeNormSq v ≤ 1 ∧ ∃ u ∈ unitCircle, D v=γ u ∨ D v= -γ u}

/-- The sign computed using a circle parameter, transporting its tangent by the matching deck map. -/
def representativeSign (D γ : Plane → Phase) (v u : Plane) : ℤ :=
  orientationSign (contactVolume (D v) (fderiv ℝ D v ![1,0]) (fderiv ℝ D v ![0,1])
    (if D v=γ u then fderiv ℝ γ u (circleTangent u) else -fderiv ℝ γ u (circleTangent u)))

/-- Choose a matching circle parameter at an intersection. Geometric applications prove
that every matching parameter gives this same sign. -/
def quotientIntersectionSign (D γ : Plane → Phase) (v : Plane) : ℤ :=
  by
  classical
  exact
  if h : v ∈ quotientIntersectionSet D γ then
    representativeSign D γ v (Classical.choose h.2)
  else 0

/-- The algebraic intersection count for finite transverse quotient intersections. -/
def algebraicIntersection (D γ : Plane → Phase)
    (h : (quotientIntersectionSet D γ).Finite) : ℤ :=
  ∑ v ∈ h.toFinset, quotientIntersectionSign D γ v

/-- Intersection count divided by the oriented boundary-covering multiplicity.
It is a relative quantity for the supplied surface and push-off. -/
def normalizedIntersection (D γ : Plane → Phase) (r : ℕ)
    (h : (quotientIntersectionSet D γ).Finite) : ℚ :=
  (algebraicIntersection D γ h : ℚ)/(r : ℚ)

/-- The unit complex direction of a nonzero coordinate vector; the value at zero
is arbitrary and is excluded in all winding applications. -/
def direction (z : ℂ) : Circle :=
  if h : z=0 then 1 else
    ⟨z/(‖z‖ : ℂ),by
      apply mem_sphere_zero_iff_norm.mpr
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_norm]
      exact div_self (norm_ne_zero_iff.mpr h)⟩

/-- A circle-valued loop has winding k when a continuous angular lift makes k full turns. -/
def HasWinding (f : ℝ → Circle) (k : ℤ) : Prop :=
  ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 (2*Real.pi)) ∧
    (∀ t ∈ Icc 0 (2*Real.pi), Circle.exp (θ t)=f t) ∧
    θ (2*Real.pi)-θ 0=2*Real.pi*(k : ℝ)

/-- Boundary tangent winding, in an extending contact trivialization, divided
by the positive boundary-covering multiplicity. -/
def HasRationalRotation (f : ℝ → Circle) (r : ℕ) (q : ℚ) : Prop :=
  0 < r ∧ ∃ k : ℤ, HasWinding f k ∧ q=(k : ℚ)/(r : ℚ)

end
end ContactTopology.RationalInvariants


