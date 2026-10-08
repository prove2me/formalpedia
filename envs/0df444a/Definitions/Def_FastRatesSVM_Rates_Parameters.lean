-- Prove2me | Definitions.Def_FastRatesSVM_Rates_Parameters
-- name    : FastRatesSVM_Rates_Parameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:34.594724+00:00
-- url     : https://prove2.me/theorems/c3eee667-c7c6-4b62-b92a-fc5e8c06e7f7
-- title:
--   Theorem 2.8 — rate exponent and sample-dependent SVM parameters
-- statement:
--   Given geometric exponent $\alpha>0$ and Tsybakov exponent $q\in[0,\infty]$, define
--   $$
--   \beta=
--   \begin{cases}
--   \alpha/(2\alpha+1),&\alpha\le(q+2)/(2q),\\
--   2\alpha(q+1)/(2\alpha(q+2)+3q+4),&\text{otherwise},
--   \end{cases}
--   \qquad
--   \lambda_n=n^{-(\alpha+1)\beta/\alpha},\quad
--   \sigma_n=n^{\beta/(\alpha d)}.
--   $$
--   For $q=\infty$ the two branches use the paper's limiting convention; for $q=0$ the first branch applies.
--
--   These are the exact rate and tuning parameters in Theorem 2.8. **Formalization Note** The theorem uses $d>0$ and $n\ge1$, so all denominators and real powers have their intended domains.
-- source:
--   Steinwart, Scovel, Fast Rates for Support Vector Machines Using Gaussian Kernels, arXiv:0708.1838v1, p. 9, Theorem 2.8 and preceding convention

import Definitions.Def_FastRatesSVM_Rates_RKHS

namespace FastRatesSVM.Rates

/-- The two cases of the exponent β in Theorem 2.8. -/
noncomputable def beta (α : ℝ) (q : ENNReal) : ℝ :=
  if q = ⊤ then
    if α ≤ 1 / 2 then α / (2 * α + 1) else 2 * α / (2 * α + 3)
  else
    if 2 * α * q.toReal ≤ q.toReal + 2 then α / (2 * α + 1)
    else 2 * α * (q.toReal + 1) /
      (2 * α * (q.toReal + 2) + 3 * q.toReal + 4)

/-- The sample-size dependent regularization parameter of Theorem 2.8. -/
noncomputable def lambdaN (α : ℝ) (q : ENNReal) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-((α + 1) / α * beta α q))

/-- The sample-size dependent Gaussian kernel parameter of Theorem 2.8. -/
noncomputable def sigmaN (d : ℕ) (α : ℝ) (q : ENNReal) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (beta α q / (α * (d : ℝ)))

end FastRatesSVM.Rates


