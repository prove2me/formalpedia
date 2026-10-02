-- Prove2me | Definitions.Def_LeblSCV_Pseudoconvex_SatisfiesContinuityPrinciple
-- name    : LeblSCV_Pseudoconvex_SatisfiesContinuityPrinciple
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T04:36:15.466461+00:00
-- url     : https://prove2.me/theorems/8d175d11-ff0b-409c-908d-e2362f5023ee
-- title:
--   Conclusion of the Kontinuitätssatz (second version)
-- statement:
--   An open set $U \subset \mathbb{C}^n$ **satisfies the continuity principle (second version)** if the following holds for every collection of closed analytic discs $\Delta_\alpha = \varphi_\alpha(\mathbb{D}) \subset U$ with boundaries $\partial\Delta_\alpha = \varphi_\alpha(\partial\mathbb{D})$:
--   $$\bigcup_\alpha \partial\Delta_\alpha \subset\subset U \implies \bigcup_\alpha \Delta_\alpha \subset\subset U.$$
--
--   This is the conclusion of Theorem 2.5.2 and condition (iv) of Theorem 2.5.6.
--
--   **Formalization Note.** The collection is a set $S$ of parametrizing maps $\varphi : \mathbb{C} \to \mathbb{C}^n$, each a closed analytic disc with $\varphi(\mathbb{D}) \subset U$. Following Definition 1.4.5, $\Delta_\alpha$ is the image of the *open* disc. Using the closed disc would give an equivalent condition, since $\varphi(\overline{\mathbb{D}}) \subset \overline{\varphi(\mathbb{D})}$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 90, Theorem 2.5.2, and p. 92, Theorem 2.5.6 (iv)

import Mathlib
import Definitions.Def_LeblSCV_Pseudoconvex_IsClosedAnalyticDisc
import Definitions.Def_LeblSCV_Pseudoconvex_IsRelCompactIn

namespace LeblSCV.Pseudoconvex

/-- The conclusion of the Kontinuitätssatz, second version (Lebl, pp. 90 and 92, Theorem 2.5.2
and Theorem 2.5.6 (iv)) for `U ⊂ ℂⁿ`: for any collection of closed analytic discs
`Δ_α = φ_α(𝔻) ⊂ U` such that `⋃_α ∂Δ_α ⊂⊂ U`, where `∂Δ_α = φ_α(∂𝔻)`, we have
`⋃_α Δ_α ⊂⊂ U`. The collection is a set `S` of parametrizing maps. -/
def SatisfiesContinuityPrinciple {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n))) : Prop :=
  ∀ S : Set (ℂ → EuclideanSpace ℂ (Fin n)),
    (∀ φ ∈ S, IsClosedAnalyticDisc φ ∧ φ '' Metric.ball (0 : ℂ) 1 ⊆ U) →
      IsRelCompactIn (⋃ φ ∈ S, φ '' Metric.sphere (0 : ℂ) 1) U →
        IsRelCompactIn (⋃ φ ∈ S, φ '' Metric.ball (0 : ℂ) 1) U

end LeblSCV.Pseudoconvex


