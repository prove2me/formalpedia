-- Prove2me | Definitions.Def_TeschlQM_Herglotz_borelTransform
-- name    : TeschlQM_Herglotz_borelTransform
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:32:53.519442+00:00
-- url     : https://prove2.me/theorems/103f51df-22c6-43a0-96cf-d21f11ffbe20
-- title:
--   Borel transform of a Borel measure on the real line (3.60)
-- statement:
--   Let $\mu$ be a Borel measure on $\mathbb{R}$. Its **Borel transform** is the function
--   $$F(z) = \int_{\mathbb{R}} \frac{1}{\lambda - z}\, d\mu(\lambda), \qquad z \in \mathbb{C}.$$
--   For a finite measure the integrand is bounded in $\lambda$ whenever $z \notin \mathbb{R}$, so $F$ is defined on $\mathbb{C} \setminus \mathbb{R}$, and more generally on the complement of the spectrum $\sigma(\mu)$.
--
--   **Formalization Note.** The integral is Mathlib's Bochner integral of `fun t : ℝ => ((t : ℂ) - z)⁻¹` against `μ`; it returns `0` when the integrand is not integrable. Every theorem of the mission assumes `IsFiniteMeasure μ` and evaluates $F$ at points where the integrand is integrable (non-real $z$), so the junk value never enters a statement.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 99, Section 3.2, Eq. (3.60)

import Mathlib

open MeasureTheory

namespace TeschlQM.Herglotz

/-- Teschl, p. 99, (3.60) (also (3.40)): the **Borel transform** of a Borel measure `μ` on `ℝ`,
`F(z) = ∫_ℝ 1/(λ − z) dμ(λ)`. -/
noncomputable def borelTransform (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂μ

end TeschlQM.Herglotz


