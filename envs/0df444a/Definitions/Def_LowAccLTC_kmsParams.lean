-- Prove2me | Definitions.Def_LowAccLTC_kmsParams
-- name    : LowAccLTC_kmsParams
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:36:37.329226+00:00
-- url     : https://prove2.me/theorems/e873e13b-542c-4ed8-83c9-b7737474f7c2
-- title:
--   The parameters $j=\lceil 10^{15}\varepsilon^{-6}\log(1/\varepsilon)\rceil$ and $\tau=1/(10^{23}(2j)^7+10)$ of §5.2
-- statement:
--   For the analysis of KMS codes the paper fixes
--   $$j=\Big\lceil 10^{15}\varepsilon^{-6}\log\tfrac1\varepsilon\Big\rceil,\qquad \tau=\frac{1}{10^{23}(2j)^7+10}.$$
--   $j$ is the rank of the faces complex $\mathcal F^jX$ used by the $j$-agreement test, and $\tau$ is the agreement threshold of Claims 5.8 and 5.12.
--
--   **Formalization Note** $\log$ is the natural logarithm.
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), §5.2 'Parameters', p.46 (PDF p.49)

import Mathlib

namespace LowAccLTC

/-! Ben Yaacov, Dikstein, Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs*,
unpublished manuscript (sha256 04242e17…); page references are printed pages (PDF page − 3). -/

/-- The rank of the faces complex used for KMS codes, `j = ⌈10^15 ε^{-6} log(1/ε)⌉`
(§5.2, "Parameters", p.46).

**Formalization Note.** `log` is the natural logarithm (the paper does not fix the base; `ln`
is the reading under which the hypotheses of Theorem 5.7 are the weakest). -/
noncomputable def kmsJ (ε : ℝ) : ℕ := ⌈(10 : ℝ) ^ 15 * ε ^ (-6 : ℤ) * Real.log (1 / ε)⌉₊

/-- `τ = 1 / (10^23 (2j)^7 + 10)` (§5.2, "Parameters", p.46). -/
noncomputable def kmsTau (ε : ℝ) : ℝ := 1 / ((10 : ℝ) ^ 23 * (2 * (kmsJ ε : ℝ)) ^ 7 + 10)

end LowAccLTC


