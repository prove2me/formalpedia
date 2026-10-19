-- Prove2me | Definitions.Def_Everyday_spacetime__e5fc57
-- name    : Everyday_spacetime
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-19T00:11:05.506357+00:00
-- url     : https://prove2.me/theorems/e5fc5728-4ad0-4f66-88d4-58e604c4d8d6
-- title:
--   Everyday spacetime: the path-integral amplitude and the gravity sector sum
-- statement:
--   The source equation writes a transition amplitude W as a path integral — the integral of the exponential of i times the action over all field configurations with momenta below the ultraviolet cutoff Λ — and integrates its action against the invariant spacetime element ∫ d⁴x √(-g), whose gravity content is the Einstein–Hilbert term (m_p²/2) R. The bundle defines the two objects that carry this structure in the mission's arena. The amplitude: on a finite configuration space C, the path integral is the finite sum over configurations of the phase exp(i S c) — the exact discrete stand-in for the source's domain of integration. And the gravity sector: on a finite spacetime X with volume weights vol standing in for the measure √(-g) d⁴x, the Einstein–Hilbert sector is the weighted sum ∑_x vol x · (m_p²/2) R x of the curvature R against the invariant volume element.
--
--   **Formalization Note** The finite configuration space is the discrete stand-in for the continuum of fields below the cutoff Λ; the finite spacetime with volume weights stands in for the invariant measure √(-g) d⁴x. The Planck mass m_p and the curvature field R are explicit real parameters; no metric or smoothness structure is claimed.
-- source:
--   Sean Carroll, "The World of Everyday Experience, In One Equation", preposterousuniverse.com, 2013-01-04, retrieved 2026-10-18, the path integral W and the gravity term (m_p²/2) R of the equation

import Mathlib

open scoped BigOperators

namespace Everyday

/-- The amplitude to undergo a transition between two configurations in
the path-integral formalism of the source equation, on a finite
configuration space: the sum over configurations of the phase
exp(i S c). The source integrates over all fields with momenta below
the ultraviolet cutoff Λ; the finite configuration space is the exact
discrete stand-in for that domain of integration. -/
noncomputable def amplitude {C : Type} [Fintype C] (S : C → ℝ) : ℂ :=
  ∑ c, Complex.exp (Complex.I * (S c : ℂ))

/-- The gravity sector of the source equation: the Einstein–Hilbert
term (m_p²/2) R integrated against the invariant volume element. The
discrete spacetime is a finite set X of points with volume weights vol
standing in for the measure √(-g) d⁴x, and R is the curvature assigned
to each point. -/
noncomputable def gravSum {X : Type} [Fintype X] (vol : X → ℝ) (mp : ℝ) (R : X → ℝ) : ℝ :=
  ∑ x, vol x * (mp ^ 2 / 2 * R x)

end Everyday


