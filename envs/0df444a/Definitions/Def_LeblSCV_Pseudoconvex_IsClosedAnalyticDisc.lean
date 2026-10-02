-- Prove2me | Definitions.Def_LeblSCV_Pseudoconvex_IsClosedAnalyticDisc
-- name    : LeblSCV_Pseudoconvex_IsClosedAnalyticDisc
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T04:25:59.834779+00:00
-- url     : https://prove2.me/theorems/a4093d98-c513-4b58-ad3e-42ced4159006
-- title:
--   Definition 1.4.5 — closed analytic disc
-- statement:
--   A nonconstant holomorphic map $\varphi : \mathbb{D} \to \mathbb{C}^n$ from the unit disc $\mathbb{D} = \{\xi \in \mathbb{C} : |\xi| < 1\}$ is an **analytic disc**. If $\varphi$ extends continuously to the closed disc $\overline{\mathbb{D}}$, the map $\varphi : \overline{\mathbb{D}} \to \mathbb{C}^n$ is a **closed analytic disc**. The image $\Delta = \varphi(\mathbb{D})$ is also called the analytic disc, and
--   $$\partial\Delta = \varphi(\partial\mathbb{D})$$
--   its boundary.
--
--   **Formalization Note.** **Formalization Note.** $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`, so its norm, balls and distances are Euclidean, as in the book. $\varphi$ is a map $\mathbb{C} \to \mathbb{C}^n$ that is continuous on the closed unit disc and holomorphic and nonconstant on the open disc. Its values off the closed disc are irrelevant. Holomorphic on an open set is `DifferentiableOn ℂ`, which is equivalent to the book's Definition 1.1.2 on open sets (Proposition 1.1.3 and Theorem 1.2.1). The definition is restated in this mission's namespace, because a draft cannot import another chapter's draft.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 34, Definition 1.4.5

import Mathlib

namespace LeblSCV.Pseudoconvex

/-- Definition 1.4.5 (Lebl, p. 34). A *closed analytic disc* is a nonconstant holomorphic map
`φ : 𝔻 → ℂⁿ` that extends continuously to the closed unit disc `closure 𝔻`. Here `φ : ℂ → ℂⁿ`
is continuous on `closure 𝔻 = Metric.closedBall 0 1`, holomorphic (`DifferentiableOn ℂ`) and
nonconstant on `𝔻 = Metric.ball 0 1`; its values off the closed disc are irrelevant. The disc is
`Δ = φ(𝔻)` and its boundary `∂Δ = φ(∂𝔻)`. -/
def IsClosedAnalyticDisc {n : ℕ} (φ : ℂ → EuclideanSpace ℂ (Fin n)) : Prop :=
  ContinuousOn φ (Metric.closedBall (0 : ℂ) 1) ∧
    DifferentiableOn ℂ φ (Metric.ball (0 : ℂ) 1) ∧
    ∃ ξ ∈ Metric.ball (0 : ℂ) 1, ∃ η ∈ Metric.ball (0 : ℂ) 1, φ ξ ≠ φ η

end LeblSCV.Pseudoconvex


