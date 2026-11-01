-- Prove2me | Definitions.Def_ShrinkingUCB_alpha
-- name    : ShrinkingUCB_alpha
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:37.396811+00:00
-- url     : https://prove2.me/theorems/16cd70c0-a2d9-4b30-b640-b80d8e88d9a9
-- title:
--   The parameter $\alpha=\sqrt{d\ln((1+N+TN)/\delta)}+1$
-- statement:
--   The input parameter of Proposition 1 and Theorem 3 is
--
--   $$
--   \alpha=\sqrt{d\ln\Big(\frac{1+N+TN}{\delta}\Big)}+1.
--   $$
--
--   The radical covers $d\ln(\cdot)$ only; the $+1$ stands outside it. The term $1+N+TN=1+(T+1)N$ comes from applying the confidence bound of Lemma 1 at the horizon $T+1$.
--
--   **Formalization Note** `Real.log` is the natural logarithm.
-- source:
--   Jin, Simchi-Levi, Wang, Wang, Yang, Shrinking the Upper Confidence Bound: A Dynamic Product Selection Problem for Urban Warehouses, arXiv:1903.07844v2, Proposition 1, p.17; Theorem 3, p.18

import Mathlib

namespace ShrinkingUCB

/-- The input parameter `α = √(d ln((1 + N + TN)/δ)) + 1` of Proposition 1 and Theorem 3
(arXiv:1903.07844v2, pp.17–18). The radical covers `d ln(…)`; the `+ 1` is outside it. `Real.log`
is the natural logarithm. -/
noncomputable def alpha (d N T : ℕ) (δ : ℝ) : ℝ :=
  √((d : ℝ) * Real.log ((1 + (N : ℝ) + (T : ℝ) * (N : ℝ)) / δ)) + 1

end ShrinkingUCB


