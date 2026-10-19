-- Prove2me | Definitions.Def_wigner
-- name    : wigner
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-18T16:48:57.287003+00:00
-- url     : https://prove2.me/theorems/c56e813a-8122-4cbf-b354-8c092c71cb16
-- title:
--   The Wigner quasiprobability distribution
-- statement:
--   The Wigner quasiprobability distribution (Wigner function) of a wavefunction. For a wavefunction $\psi : \mathbb{R} \to \mathbb{C}$ and a phase-space point $(x, p) \in \mathbb{R}^2$, with $\hbar > 0$ the reduced Planck constant, the Wigner function is
--
--   $$W(x,p) = \frac{1}{\pi\hbar}\int_{-\infty}^{\infty}\overline{\psi(x+y)}\,\psi(x-y)\,e^{2ipy/\hbar}\,dy,$$
--
--   the transform introduced by E. Wigner in 1932 to study quantum corrections to classical statistical mechanics. It is the phase-space realization of the quantum state: integrating $W$ over momentum recovers the position probability density, integrating over position recovers the momentum density, and operator expectation values become phase-space averages against $W$ via Weyl quantization.
--
--   **Formalization Note** The integral is the Bochner integral with respect to Lebesgue measure on $\mathbb{R}$. The code factors the formula into the integrand (Wigner.wignerIntegrand), the integral (Wigner.wignerIntegral), and the Wigner function itself (Wigner.wigner), defined as the real part of the integral divided by $\pi\hbar$. That the discarded imaginary part vanishes is Property 1 of the source and the mission's first milestone; the definition is total, with value 0 wherever the integral does not exist.
-- source:
--   Wikipedia, "Wigner quasiprobability distribution" (oldid 1376057304), section "Definition and meaning", first displayed formula. https://en.wikipedia.org/wiki/Wigner_quasiprobability_distribution

import Mathlib

open MeasureTheory
open ComplexConjugate

namespace Wigner

/-- The integrand of the Wigner function of the wavefunction psi at the phase-space
point (x, p), with hbar the reduced Planck constant:
conj (psi (x + y)) * psi (x - y) * exp (2 * p * y * i / hbar). -/
noncomputable def wignerIntegrand (ψ : ℝ → ℂ) (ℏ x p y : ℝ) : ℂ :=
  conj (ψ (x + y)) * ψ (x - y) *
    Complex.exp (Complex.ofReal (2 * p * y / ℏ) * Complex.I)

/-- The defining integral of the Wigner function of psi at (x, p):
the Bochner integral over y of wignerIntegrand psi hbar x p y. -/
noncomputable def wignerIntegral (ψ : ℝ → ℂ) (ℏ x p : ℝ) : ℂ :=
  ∫ y, wignerIntegrand ψ ℏ x p y

/-- The Wigner quasiprobability distribution (Wigner function) of psi at (x, p):
the real part of wignerIntegral, divided by pi * hbar. -/
noncomputable def wigner (ψ : ℝ → ℂ) (ℏ x p : ℝ) : ℝ :=
  (wignerIntegral ψ ℏ x p).re / (Real.pi * ℏ)

end Wigner


