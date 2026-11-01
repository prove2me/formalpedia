-- Prove2me | Definitions.Def_MNLStability_scaleProd
-- name    : MNLStability_scaleProd
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:05.551482+00:00
-- url     : https://prove2.me/theorems/5a151915-0c83-4373-b015-8345a7b6851f
-- title:
--   Scaled weights: one product, or the no-purchase option
-- statement:
--   1. **Scaling a product** (§2.1): for a product $a$ and $\varepsilon\in[0,1)$, $\tilde w_a=(1-\varepsilon)w_a$ and $\tilde w_i=w_i$ for every other product and for the no-purchase option.
--   2. **Scaling the no-purchase option** (proof of Lemma 5): $\tilde w_0=(1-\varepsilon)w_0$ and every product weight is unchanged.
--
--   Theorem 2 compares expected demands under $w$ and the first scaling; the second is needed when Lemma 5 rounds the no-purchase weight.
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §2.1, p.10; proof of Lemma 5, p.17

import Mathlib
import Definitions.Def_MNLStability_Weights

namespace MNLStability

variable {n : ℕ}

/-- The scaled weights `w̃` of SSRN:3498325, §2.1, p.10: the weight of product `a` becomes
`w̃_a = (1 − ε) · w_a`, and `w̃_i = w_i` for every other product and for the no-purchase option. -/
noncomputable def scaleProd (wts : Weights n) (a : Fin n) (ε : ℝ) : Weights n :=
  ⟨wts.w0, Function.update wts.w a ((1 - ε) * wts.w a)⟩

/-- The no-purchase weight scaled to `(1 − ε) · w₀`, all product weights unchanged (the rounding of
the no-purchase weight in the proof of Lemma 5, SSRN:3498325, p.17). -/
noncomputable def scaleNoPurchase (wts : Weights n) (ε : ℝ) : Weights n :=
  ⟨(1 - ε) * wts.w0, wts.w⟩

end MNLStability


