-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_mThree
-- name    : AutobidSPPE_Supplement_mThree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:48:00.755583+00:00
-- url     : https://prove2.me/theorems/5ce5691c-40a7-48cf-8138-cfea2f0caab5
-- title:
--   Three-bidder certificate value $m$ of (61)
-- statement:
--   $$
--   m=\min\Big\{1,\ \frac{l^2A^3}{6U^2},\ \frac{l^2A^6}{72U^4},\ \frac{l^3A^9}{216U^6}\Big\},\qquad A=\min_i\bar v_i,
--   $$
--   with $U=\max_i\hat v_i$ and $l=\min_i\underline\alpha_i$. Lemma 3.4 shows that for three bidders it satisfies certificate (60).
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (61), p.28; Lemma 3.4, p.30

import Mathlib
import Definitions.Def_AutobidSPPE_supU
import Definitions.Def_AutobidSPPE_Supplement_lLow

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- The explicit three-bidder certificate (61)
`m = min{1, l²A³/(6U²), l²A⁶/(72U⁴), l³A⁹/(216U⁶)}`, `A = minᵢ v̄ᵢ` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (61), p.28; Lemma 3.4, p.30).

**Formalization Note** `A = ⨅ i, v̄ᵢ` uses the actual supports, `U = maxᵢ v̂ᵢ` and `l = minᵢ α̲ᵢ` use the
certified bounds and the budgets, as on p.28. -/
noncomputable def mThree {n : ℕ} (vbar vhat ρ : Fin n → ℝ) : ℝ :=
  let A : ℝ := ⨅ i, vbar i
  let U : ℝ := supU vhat
  let l : ℝ := lLow vhat ρ
  min 1 (min (l ^ 2 * A ^ 3 / (6 * U ^ 2)) (min (l ^ 2 * A ^ 6 / (72 * U ^ 4)) (l ^ 3 * A ^ 9 / (216 * U ^ 6))))

end AutobidSPPE.Supplement


