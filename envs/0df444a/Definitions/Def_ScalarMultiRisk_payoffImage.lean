-- Prove2me | Definitions.Def_ScalarMultiRisk_payoffImage
-- name    : ScalarMultiRisk_payoffImage
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:16:16.170522+00:00
-- url     : https://prove2.me/theorems/78961b23-8788-42d0-9b5a-fb6c76ee8619
-- title:
--   The image $S^{\mathsf T}\mathcal D$ of a set of portfolios
-- statement:
--   For a price $S$ and a set $\mathcal D$ of portfolios, $S^{\mathsf T}\mathcal D=\{S^{\mathsf T}X\mid X\in\mathcal D\}$.
--
--   **Formalization Note** The image is taken up to a.e. equality, since portfolios are a.e.-classes in the paper.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Corollaries 4.10, 4.11, pp.22–23

import Mathlib
import Definitions.Def_ScalarMultiRisk_payoff

open MeasureTheory

namespace ScalarMultiRisk

/-- **The image `S^T 𝒟`.** arXiv:1807.10694v5, Corollary 4.10, p.22, and Corollary 4.11, p.23:
`S^T 𝒟 := {S^T X | X ∈ 𝒟}` for a set `𝒟` of portfolios.

**Formalization Note.** Portfolios are classes in the paper, so the image is taken up to
`P`-a.e. equality. -/
def payoffImage {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) (S : Ω → Fin d → ℝ)
    (C : Set (Ω → Fin d → ℝ)) : Set (Ω → ℝ) :=
  {Z | ∃ X ∈ C, Z =ᵐ[P] payoff S X}

end ScalarMultiRisk


