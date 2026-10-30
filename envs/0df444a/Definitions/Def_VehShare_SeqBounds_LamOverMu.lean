-- Prove2me | Definitions.Def_VehShare_SeqBounds_LamOverMu
-- name    : VehShare_SeqBounds_LamOverMu
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:33:15.480786+00:00
-- url     : https://prove2.me/theorems/61100b31-7cee-41ad-8c44-554ad7e33aa6
-- title:
--   The constant $\Lambda/\mu$
-- statement:
--   With $\Lambda=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}$ and $\frac1\mu=\sum_{(i,j)\in\mathcal A}\frac{\Lambda_{ij}}{\Lambda\mu_{ij}}$ (Theorem 1, p. 7), the constant of the bound is
--
--   $$
--   \frac{\Lambda}{\mu}=\sum_{i,j}\frac{\Lambda_{ij}}{\mu_{ij}}.
--   $$
--
--   It is the expected number of vehicles in transit when every customer is served.
--
--   **Formalization Note** When $\Lambda>0$ this is the paper's $\Lambda\cdot\frac1\mu$; when $\Lambda=0$ the paper's $1/\mu$ is $0/0$ and the sum is $0$.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, Theorem 1, p. 7

import Mathlib
import Definitions.Def_VehShare_SeqBounds_meanTime

namespace VehShare.SeqBounds

/-- **The constant `Λ/μ`.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), Theorem 1, p. 7: "`Λ = ∑_{(i,j)∈𝒜} Λ_ij` and `1/μ = ∑_{(i,j)∈𝒜} Λ_ij/(Λ μ_ij)`".

`LamOverMu P = ∑_{i,j} Λ_ij / μ_ij`, the product `Λ · (1/μ)`.

**Formalization Note.** When `Λ > 0` this is the paper's `Λ/μ`; when `Λ = 0` the paper's `1/μ` is
`0/0` and the sum is 0. Pairs with `Λ_ij = 0` (outside `𝒜`) contribute 0. -/
noncomputable def LamOverMu (P : Instance) : ℝ :=
  ∑ i, ∑ j, P.Λ i j * meanTime P i j

end VehShare.SeqBounds


