-- Prove2me | Definitions.Def_LeblSCV_BallPolydisc_unitPolydisc
-- name    : LeblSCV_BallPolydisc_unitPolydisc
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:16:32.791543+00:00
-- url     : https://prove2.me/theorems/702f4261-201b-4a90-af74-85cec3f87748
-- title:
--   Unit polydisc $\mathbb{D}^n$
-- statement:
--   The **unit polydisc** of $\mathbb{C}^n$ is the product of $n$ copies of the unit disc $\mathbb{D} = \{\zeta \in \mathbb{C} : |\zeta| < 1\}$:
--   $$\mathbb{D}^n = \{ z \in \mathbb{C}^n : |z_k| < 1 \text{ for } k = 1, \dots, n \}.$$
--   For $n = 2$ it is the unit bidisc $\mathbb{D}^2 = \mathbb{D} \times \mathbb{D}$.
--
--   **Formalization Note.** $\mathbb{C}^n$ is `Fin n → ℂ`, and $|z_k|$ is the complex absolute value `‖z k‖`. (This set coincides with Mathlib's sup-norm unit ball `Metric.ball 0 1`; it is written coordinatewise to make the distinction from $\mathbb{B}_n$ visible.)
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 32 (display defining 𝔹_n and 𝔻^n)

import Mathlib

namespace LeblSCV.BallPolydisc

/-- The unit polydisc `𝔻ⁿ = {z ∈ ℂⁿ : |z_k| < 1 for k = 1, …, n}` of Lebl, p. 32. -/
def unitPolydisc (n : ℕ) : Set (Fin n → ℂ) :=
  {z | ∀ k : Fin n, ‖z k‖ < 1}

end LeblSCV.BallPolydisc


