-- Prove2me | Definitions.Def_SecondBestMatch_contractRegion
-- name    : SecondBestMatch_contractRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:51.562458+00:00
-- url     : https://prove2.me/theorems/015d9e85-53d1-4434-a08c-3da1d2a4cb17
-- title:
--   Contracted region $\mathcal D_Z$
-- statement:
--   For a multiplier $\alpha$, a realization $z$ of $Z$ and a rank region $\mathcal D\subseteq(0,1)^2$ (buyer rank $\rho$, seller rank $\sigma$), let $\theta = z^{\alpha/(1+\alpha)}$ and $\eta = (1-z)^{\alpha/(1+\alpha)}$. The **contracted region** is
--   $$
--   \mathcal D_Z = \{(\theta\rho,\ \eta\sigma) : (\rho,\sigma)\in\mathcal D\}.
--   $$
--   The buyer coordinate is scaled by $\theta$, the seller coordinate by $\eta$.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 4.2, p.14

import Mathlib

open MeasureTheory Set

namespace SecondBestMatch

/-- The contracted region `𝒟_Z = {(θρ, ησ) : (ρ, σ) ∈ 𝒟}` with `θ = Z^{α/(1+α)}` (buyer rank) and
`η = (1 − Z)^{α/(1+α)}` (seller rank), at the realization `z` of `Z` (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §4.2, p.14). -/
def contractRegion (α z : ℝ) (D : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  (fun p : ℝ × ℝ => (z ^ (α / (1 + α)) * p.1, (1 - z) ^ (α / (1 + α)) * p.2)) '' D

end SecondBestMatch


