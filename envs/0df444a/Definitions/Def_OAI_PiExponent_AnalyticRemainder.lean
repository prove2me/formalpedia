-- Prove2me | Definitions.Def_OAI_PiExponent_AnalyticRemainder
-- name    : OAI_PiExponent_AnalyticRemainder
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-07T19:41:30.829758+00:00
-- url     : https://prove2.me/theorems/1af087c1-f65e-41b5-90e3-ea99fecb6829
-- title:
--   Explicit collision and translation error for the fixed determinant family
-- statement:
--   For a fixed admissible determinant family, write $M(H)$ for the row count, and let $m$ and $v_0$ be its dimension and row scale. Define
--
--   $$Q(H)=(H+1)^{2m}(H/v_0+1),\qquad s=\exp(-\log2/2),$$
--
--   $$\varepsilon_d(H)=\frac{\log M(H)+\log2/4-\log(1-s)}{H}+\frac{\log Q(H)}{H}.$$
--
--   For positive heights, $Q(H)$ majorizes the natural-floor translation count in the pinned source. The first error term is the source's normalized factorial and geometric collision correction. These explicit functions allow the finite determinant estimate and the vanishing-error argument to be treated separately. This definition asserts neither estimate nor convergence.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/CollisionExponential.lean (collisionRatio, collisionRemainder); https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean (translationTermCount). Q is the real polynomial upper envelope obtained by replacing each natural floor by its argument at positive heights.

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily

noncomputable section
namespace OAI.PiExponent.DeterminantContradiction

-- Real polynomial majorant of TranslationCountLimit.translationTermCount.
def translationEnvelope (m : ℕ) (v H : ℝ) : ℝ :=
  (H + 1) ^ (2 * m) * (H / v + 1)

-- CollisionExponential.collisionRemainder, plus the translation entropy.
def analyticRemainder {nu : ℝ} (d : FixedData nu) (H : ℝ) : ℝ :=
  (Real.log (actualRowCount d H : ℝ) + Real.log 2 / 4 -
    Real.log (1 - Real.exp (-Real.log 2 / 2))) / H +
    Real.log (translationEnvelope d.m d.v0 H) / H

end OAI.PiExponent.DeterminantContradiction


