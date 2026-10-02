-- Prove2me | Definitions.Def_LeblSCV_BallPolydisc_IsAnalyticDisc
-- name    : LeblSCV_BallPolydisc_IsAnalyticDisc
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:17:18.069409+00:00
-- url     : https://prove2.me/theorems/8a0c2432-db1f-4b5a-b59a-abf64b92323f
-- title:
--   Definition 1.4.5 — analytic disc
-- statement:
--   Let $\mathbb{D} = \{\zeta \in \mathbb{C} : |\zeta| < 1\}$ be the unit disc. A nonconstant holomorphic mapping
--   $$\varphi : \mathbb{D} \to \mathbb{C}^n$$
--   is called an **analytic disc**. "Nonconstant" means that $\varphi(\zeta) \ne \varphi(\zeta')$ for some $\zeta, \zeta' \in \mathbb{D}$.
--
--   Analytic discs play the role of line segments in $\mathbb{C}^n$ and let one-variable results be applied in several variables; they are central to the boundary behaviour of holomorphic functions.
--
--   **Formalization Note.** $\varphi$ is a function `ℂ → (Fin n → ℂ)` of which only the values on `Metric.ball 0 1` (the unit disc) matter; holomorphic is `DifferentiableOn ℂ` on the open disc. The second half of Definition 1.4.5 (closed analytic discs) is not used by this mission and is not formalized.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 34, Definition 1.4.5

import Mathlib

namespace LeblSCV.BallPolydisc

/-- Definition 1.4.5 (Lebl, p. 34). An analytic disc is a nonconstant holomorphic mapping
`φ : 𝔻 → ℂⁿ`, where `𝔻 = {ζ ∈ ℂ : |ζ| < 1}`. Only the values of `φ` on `𝔻` matter. -/
def IsAnalyticDisc {n : ℕ} (φ : ℂ → (Fin n → ℂ)) : Prop :=
  DifferentiableOn ℂ φ (Metric.ball (0 : ℂ) 1) ∧
    ∃ z ∈ Metric.ball (0 : ℂ) 1, ∃ w ∈ Metric.ball (0 : ℂ) 1, φ z ≠ φ w

end LeblSCV.BallPolydisc


