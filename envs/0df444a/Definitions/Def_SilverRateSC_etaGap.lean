-- Prove2me | Definitions.Def_SilverRateSC_etaGap
-- name    : SilverRateSC_etaGap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:45:06.084225+00:00
-- url     : https://prove2.me/theorems/9cee8512-2238-4c1a-bb0b-c05f891aeee3
-- title:
--   Contraction factors $\chi_i$ and $\eta_i$, (7)
-- statement:
--   For the gap stepsizes $h_t$, $t_{i-1}<t<t_i$, between two checkpoints, an input threshold $\ell_i$ and an excess $D_i>0$,
--   $$\chi_i:=\prod_{t_{i-1}<t<t_i}\Bigl(1-\frac{h_t}{\kappa}\Bigr),\qquad \eta_i:=\chi_i-(1-\chi_i)\frac{\ell_i}{D_i},$$
--   so that $\chi_i(\ell_i+D_i)-\ell_i=D_i\eta_i$: the quadratic term alone scales the input coordinate by $\chi_i$, and $\eta_i$ is the fraction of the excess above $\ell_i$ that survives the gap. An empty gap has $\chi_i=\eta_i=1$.
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), §2.2, (7), p.11

import Mathlib

namespace SilverRateSC

/-- The contraction factor `χ_i := ∏ (1 − h_t/κ)` over the gap stepsizes, (7). -/
noncomputable def chiGap (κ : ℝ) (hs : List ℝ) : ℝ := (hs.map (fun h => 1 - h / κ)).prod

/-- **Contraction factors** (7): for the gap stepsizes `hs` between two checkpoints,
`χ_i := ∏_{t_{i−1} < t < t_i} (1 − h_t/κ)` and `η_i := χ_i − (1 − χ_i) ℓ_i / D_i`, so that
`χ_i(ℓ_i + D_i) − ℓ_i = D_i η_i`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, §2.2, (7), p. 11.

**Formalization Note** The gap is given by its list of stepsizes; an empty gap has `χ = η = 1`.
Statements using `η_i` assume `D_i > 0`. -/
noncomputable def etaGap (κ : ℝ) (hs : List ℝ) (ℓ D : ℝ) : ℝ :=
  chiGap κ hs - (1 - chiGap κ hs) * ℓ / D

end SilverRateSC


