-- Prove2me | Definitions.Def_TorusEuler_Riccati
-- name    : TorusEuler_Riccati
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T19:37:26.743112+00:00
-- url     : https://prove2.me/theorems/9999b7ac-d3fe-433d-a4ac-a5c346cbe741
-- title:
--   Coefficients of the Riccati reference equation
-- statement:
--   The scalar coefficients of the reference Riccati equation (cc:eq:model) used in Lemma 2.4. For $\varepsilon,\tau\in\mathbb{R}$ set
--   $$x(\varepsilon,\tau)=\frac{\varepsilon\tau^2}{2},\qquad s(\varepsilon,\tau)=\frac{1}{\sqrt{1+x(\varepsilon,\tau)^2}},$$
--   $$\mathrm{damping}=2\varepsilon\tau\,x\,s^2,\qquad \mathrm{driving}=s^2(1-\varepsilon x),$$
--   so that the Riccati right-hand side is
--   $$\mathrm{rhs}(\varepsilon,\tau,y)=s^2\bigl(1-\varepsilon x-2\varepsilon\tau x\,y\bigr)-y^2.$$
--   The reference solution form is $\mathrm{referenceY}(\varepsilon,e,\tau)=s(\varepsilon,\tau)\bigl(1+e(\tau)\bigr)-\tfrac12\varepsilon\tau\,x\,s^2$, where $e$ is a small deviation function. These coefficients are the frozen-coefficient model of the amplification of a new wave over the preceding one.
-- source:
--   Alpöge–Buckmaster–Coiculescu, *Finite-Time Singularity Formation for the Three-Dimensional Euler Equations*, frozen manuscript of 18 November 2026 (torus-paper-freeze-2026-11-18). Lean: https://github.com/mcoiculescu/EulerBlowupPublic/blob/36d3961161f8e7bba9cc8f671e5d0c4a27281239/formalization/lean/TorusEuler/ReferenceRiccati.lean#L20-L35; TeX: https://github.com/mcoiculescu/EulerBlowupPublic/blob/36d3961161f8e7bba9cc8f671e5d0c4a27281239/frozen-manuscript/sections/03_amplification.tex (cc:eq:model).

import Mathlib

namespace TorusEuler.ReferenceRiccati

noncomputable section

def x (ε τ : ℝ) : ℝ := ε * τ ^ 2 / 2

def s (ε τ : ℝ) : ℝ := (Real.sqrt (1 + x ε τ ^ 2))⁻¹

def damping (ε τ : ℝ) : ℝ := 2 * ε * τ * x ε τ * s ε τ ^ 2

def driving (ε τ : ℝ) : ℝ := s ε τ ^ 2 * (1 - ε * x ε τ)

def rhs (ε τ y : ℝ) : ℝ := driving ε τ - damping ε τ * y - y ^ 2

def referenceY (ε : ℝ) (e : ℝ → ℝ) (τ : ℝ) : ℝ :=
  s ε τ * (1 + e τ) - damping ε τ / 4

end

end TorusEuler.ReferenceRiccati


