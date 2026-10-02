-- Prove2me | Definitions.Def_LeblSCV_BallPolydisc_ContainsNoAnalyticDiscs
-- name    : LeblSCV_BallPolydisc_ContainsNoAnalyticDiscs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:17:56.315041+00:00
-- url     : https://prove2.me/theorems/3153a61a-3cc5-4f94-9adf-2393744523b5
-- title:
--   A set containing no analytic discs
-- statement:
--   A set $S \subset \mathbb{C}^n$ **contains no analytic discs** if there is no analytic disc $\varphi : \mathbb{D} \to \mathbb{C}^n$ with
--   $$\varphi(\mathbb{D}) \subset S.$$
--   The boundary of the bidisc contains analytic discs (e.g. $\{p\} \times \mathbb{D}$ for $|p| = 1$); the unit sphere does not.
--
--   **Formalization Note.** "Analytic disc" is `IsAnalyticDisc`; $\varphi(\mathbb{D}) \subset S$ is `Set.MapsTo φ (Metric.ball 0 1) S`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), pp. 34 and 36 (usage in Proposition 1.4.6 and Theorem 1.4.8)

import Mathlib
import Definitions.Def_LeblSCV_BallPolydisc_IsAnalyticDisc

namespace LeblSCV.BallPolydisc

/-- A set `S ⊆ ℂⁿ` contains no analytic discs (Lebl, pp. 34, 36): there is no analytic disc
`φ : 𝔻 → ℂⁿ` with `φ(𝔻) ⊆ S`. -/
def ContainsNoAnalyticDiscs {n : ℕ} (S : Set (Fin n → ℂ)) : Prop :=
  ∀ φ : ℂ → (Fin n → ℂ), IsAnalyticDisc φ → ¬ Set.MapsTo φ (Metric.ball (0 : ℂ) 1) S

end LeblSCV.BallPolydisc


