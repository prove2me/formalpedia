-- Prove2me | Definitions.Def_DivideChooseBayes_algDelta
-- name    : DivideChooseBayes_algDelta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:26:15.061879+00:00
-- url     : https://prove2.me/theorems/d8704915-13ce-44d9-b94e-f85f0b0c0a26
-- title:
--   Step size $\delta = \gamma / \sum_i |g^D_i|$ of Algorithm 1
-- statement:
--   Algorithm 1 sets its step size to
--
--   $$\delta := \frac{\gamma}{\sum_{i=1}^n |g^D_i|},$$
--
--   where $\gamma$ is the additive error bound and the divider values $g^D$ are not all zero.
--
--   **Formalization Note** The theorems assume $g^D\ne 0$ and $\gamma>0$, so $\delta>0$.
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, Algorithm 1, line 1, p.9

import Mathlib

namespace DivideChooseBayes

/-- **Step size `δ` of Algorithm 1.**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, Algorithm 1, line 1, p.9: `δ ← γ / ∑ᵢ |gᴰᵢ|`.

**Formalization Note.** The algorithm's input requires `gᴰ` not all zero, so the denominator is
positive wherever the theorems use `δ`. -/
noncomputable def algDelta {ι : Type*} [Fintype ι] (gD : ι → ℝ) (γ : ℝ) : ℝ :=
  γ / ∑ i, |gD i|

end DivideChooseBayes


