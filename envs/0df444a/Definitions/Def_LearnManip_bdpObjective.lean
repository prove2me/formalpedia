-- Prove2me | Definitions.Def_LearnManip_bdpObjective
-- name    : LearnManip_bdpObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:46.690722+00:00
-- url     : https://prove2.me/theorems/285200df-6d6a-4d56-a605-13e97669cd3f
-- title:
--   Objective of the BDP equation (10)
-- statement:
--   For a function $v(\mu,s,c)$, the objective of the Bayesian dynamic programming equation (10) at a quantity $q$ and a distorted law $G$:
--   $$-cq+\int\Bigl(y+\alpha v\bigl(y,\tfrac{s}{1+sq},c\eta\bigr)\Bigr)\,dG(y)-\gamma D\bigl(G\,\|\,N(\mu,\sigma^2_{\mu^q})\bigr).$$
--
--   **Formalization Note.** This is used only for $G$ of finite relative entropy, since the real part of an infinite relative entropy is $0$ in Lean. The integrand is $G$-integrable for every $v$ the mission applies it to.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (10), p.12

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_postVar
import Definitions.Def_LearnManip_baseLaw

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The objective of the BDP equation (10), p.12, of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04), at
the quantity `q` and the distorted law `G`:
`−c q + E_G[y + α v(y, s/(1+sq), cη)] − γ KL(G ‖ N(μ, σ²_{μ^q}))`.

**Formalization Note.** `toReal ∞ = 0`, so this is meaningful only for `G` of finite relative entropy;
every use sits under `klDiv … ≠ ∞`. The integral is the Bochner integral: it is the paper's whenever
`y ↦ v y _ _` is `G`-integrable, which holds for every `v` this development applies it to (`InClass`,
`sepValue`), since `y` is `G`-integrable. -/
noncomputable def bdpObjective (P : Params) (v : ℝ → ℝ≥0 → ℝ≥0 → ℝ) (μ : ℝ) (s c q : ℝ≥0)
    (G : Measure ℝ) : ℝ :=
  -((c : ℝ) * q) + ∫ y, (y + (P.α : ℝ) * v y (postVar s q) (c * P.η)) ∂G
    - (P.γ : ℝ) * (InformationTheory.klDiv G (baseLaw μ s q)).toReal

end LearnManip


