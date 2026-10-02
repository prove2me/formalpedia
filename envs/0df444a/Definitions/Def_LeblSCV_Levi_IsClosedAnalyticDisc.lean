-- Prove2me | Definitions.Def_LeblSCV_Levi_IsClosedAnalyticDisc
-- name    : LeblSCV_Levi_IsClosedAnalyticDisc
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:58:27.149571+00:00
-- url     : https://prove2.me/theorems/f7a1ae39-a89a-43f5-a0e5-da0ab8d58ffe
-- title:
--   Definition 1.4.5 — closed analytic disc
-- statement:
--   An **analytic disc** is a nonconstant holomorphic map $\varphi : \mathbb{D} \to \mathbb{C}^n$, where $\mathbb{D} = \{\xi \in \mathbb{C} : |\xi| < 1\}$. If $\varphi$ extends continuously to the closed unit disc $\overline{\mathbb{D}}$, the map $\varphi : \overline{\mathbb{D}} \to \mathbb{C}^n$ is a **closed analytic disc**.
--
--   **Formalization Note.** `IsClosedAnalyticDisc φ` for an ambient map `φ : ℂ → (Fin n → ℂ)`: continuous on `Metric.closedBall 0 1`, `DifferentiableOn ℂ` on `Metric.ball 0 1`, and not constant on `Metric.ball 0 1`. Values off the closed disc are irrelevant.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 34, Definition 1.4.5

import Mathlib

namespace LeblSCV.Levi

/-- Definition 1.4.5 (Lebl, p. 34). A *closed analytic disc* is a map `φ : ℂ → ℂⁿ` that is
holomorphic and nonconstant on the open unit disc `𝔻` and continuous on the closed unit disc
`closure 𝔻` (values off the closed disc are irrelevant). -/
def IsClosedAnalyticDisc {n : ℕ} (φ : ℂ → (Fin n → ℂ)) : Prop :=
  ContinuousOn φ (Metric.closedBall (0 : ℂ) 1) ∧
    DifferentiableOn ℂ φ (Metric.ball (0 : ℂ) 1) ∧
    ∃ ξ ∈ Metric.ball (0 : ℂ) 1, ∃ η ∈ Metric.ball (0 : ℂ) 1, φ ξ ≠ φ η

end LeblSCV.Levi


