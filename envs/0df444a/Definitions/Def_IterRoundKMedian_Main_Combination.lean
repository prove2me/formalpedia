-- Prove2me | Definitions.Def_IterRoundKMedian_Main_Combination
-- name    : IterRoundKMedian_Main_Combination
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:25:29.855642+00:00
-- url     : https://prove2.me/theorems/44b95c47-abb1-4b27-85ba-6b7fc5f41b9c
-- title:
--   The constants a, b, c, u⋆, β⋆, α⋆ of (92)
-- statement:
--   The constants of (92) are
--   $$a=\tfrac{91}{12},\quad b=\sqrt{90/e},\quad c=1-\tfrac2e,\quad u_\star=\frac{2c}{b+\sqrt{b^2+4ac}},\quad \beta_\star=u_\star^2,\quad \alpha_\star=2-\frac{\beta_\star}{12}.$$
--   $u_\star$ is the positive root of $au^2+bu-c=0$, and $\beta_\star$ is where $f(\beta)=2-\beta/12$ meets $g(\beta)=1+\frac2e+\sqrt{90\beta/e}+\frac{15}{2}\beta$.
--
--   **Formalization Note.** Namespace `Combination`; `alphaStar` is the closed form, not a decimal.
-- source:
--   Byrka, Guo, Hu, Li, Shin, Vajanopath, Wan, Wang, Iterative Randomized Rounding for k-Median in General and Euclidean Metrics, STOC 2027 submission (manuscript sha256 02f6267b…), p. 71, Lemma 8.1, (92)

import Mathlib

namespace IterRoundKMedian.Main
namespace Combination

/-- `a = 91/12` in (92). -/
noncomputable def a : ℝ := 91 / 12

/-- `b = √(90/e)` in (92). -/
noncomputable def b : ℝ := Real.sqrt (90 / Real.exp 1)

/-- `c = 1 − 2/e` in (92). -/
noncomputable def c : ℝ := 1 - 2 / Real.exp 1

/-- `u⋆ = 2c / (b + √(b² + 4ac))`, the positive root of `a u² + b u − c = 0`. -/
noncomputable def uStar : ℝ := 2 * c / (b + Real.sqrt (b ^ 2 + 4 * a * c))

/-- `β⋆ = (u⋆)²`. -/
noncomputable def betaStar : ℝ := uStar ^ 2

/-- `α⋆ = 2 − β⋆/12`. -/
noncomputable def alphaStar : ℝ := 2 - betaStar / 12

end Combination
end IterRoundKMedian.Main


