-- Prove2me | Definitions.Def_InfoBargaining_SellerPayoff_priorMean
-- name    : InfoBargaining_SellerPayoff_priorMean
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:10:35.925912+00:00
-- url     : https://prove2.me/theorems/34b0f519-0d57-4006-b252-8a23774d09c6
-- title:
--   Prior mean $\hat u=\int u\,dF(u)$
-- statement:
--   For a prior law $\mu$ of the buyer's value $u$ (the distribution $F$ of p. 7), the **prior mean** is
--
--   $$
--   \hat u=\int u\,d\mu(u).
--   $$
--
--   It is the rotation point of the posterior-mean distributions $G(\cdot,\alpha)$ and the peak of the value of information in the seller's cost.
--
--   **Formalization Note** A Bochner integral, equal to $0$ when $u\mapsto u$ is not integrable; every prior in this mission has a finite mean.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), §2, unnumbered, p. 7 ("a finite mean û > 0")

import Mathlib

open MeasureTheory

namespace InfoBargaining.SellerPayoff

/-- **The prior mean `û` of the buyer's value.**
Guo, *Gathering Information before Negotiation*, SSRN 3930651 (manuscript of 15 Feb 2022),
§2, p. 7: "u is drawn from … F(u) on [u̲, ū] … and a finite mean û > 0".

`priorMean μ = ∫ u dμ(u)`.

**Formalization Note.** A Bochner integral: it is `0` when `u ↦ u` is not `μ`-integrable.
Every prior used in this mission has a finite mean. -/
noncomputable def priorMean (μ : Measure ℝ) : ℝ := ∫ u, u ∂μ

end InfoBargaining.SellerPayoff


