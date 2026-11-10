-- Prove2me | Definitions.Def_NearOptOWF_nmCAPPNo
-- name    : NearOptOWF_nmCAPPNo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:50:22.189+00:00
-- url     : https://prove2.me/theorems/35ccd304-1bc9-4690-92d4-89724b666523
-- title:
--   No-instances of nmCAPP
-- statement:
--   The **no-instances** of nmCAPP are those with $\beta \in [2^n]$, $k = 1/\epsilon \ge 1$ and
--   $$
--   \Pr_x[C(x) = 1] < \frac{\beta}{2^n}.
--   $$
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 3.1, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_NearOptOWF_NmCAPPInst_accFrac

namespace NearOptOWF

/-- The **no-instances of nmCAPP** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 3.1, p.8 (PDF p.10): "Reject: if `Pr_x[C(x) =
1] < β/2ⁿ`"), among the instances with `β ∈ [2ⁿ]` and `k = 1/ε ≥ 1`. -/
def nmCAPPNo : Set NmCAPPInst :=
  {I | 1 ≤ I.β ∧ I.β ≤ 2 ^ I.n ∧ 1 ≤ I.k ∧ I.accFrac < I.β / 2 ^ I.n}

end NearOptOWF


