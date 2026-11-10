-- Prove2me | Definitions.Def_NearOptOWF_nmCAPPYes
-- name    : NearOptOWF_nmCAPPYes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:50:11.307001+00:00
-- url     : https://prove2.me/theorems/9957a26e-89d4-497b-9dc0-87c2300e879d
-- title:
--   Yes-instances of nmCAPP
-- statement:
--   The **yes-instances** of nmCAPP are those with $\beta \in [2^n]$, $k = 1/\epsilon \ge 1$ and
--   $$
--   \Pr_x[C(x) = 1] \ge (1 + \epsilon)\,\frac{\beta}{2^n}.
--   $$
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 3.1, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_NearOptOWF_NmCAPPInst_accFrac

namespace NearOptOWF

/-- The **yes-instances of nmCAPP** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 3.1, p.8 (PDF p.10): "Accept: if `Pr_x[C(x) =
1] ≥ (1 + ε) β/2ⁿ`"), among the instances with `β ∈ [2ⁿ]` and `k = 1/ε ≥ 1`. -/
def nmCAPPYes : Set NmCAPPInst :=
  {I | 1 ≤ I.β ∧ I.β ≤ 2 ^ I.n ∧ 1 ≤ I.k ∧
    (1 + 1 / (I.k : ℝ)) * I.β / 2 ^ I.n ≤ I.accFrac}

end NearOptOWF


