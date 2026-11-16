-- Prove2me | Definitions.Def_RecruitSmaller_Supplement_gft
-- name    : RecruitSmaller_Supplement_gft
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:55:59.5523+00:00
-- url     : https://prove2.me/theorems/2e0cd7b7-15f0-4cf0-85c9-69365f438d9d
-- title:
--   Realized expected Gains From Trade $\mathrm{gft}_M(b,s)$
-- statement:
--   Under truthful reporting, the **realized expected Gains From Trade** of a mechanism $M$ at the profile $(b,s)$ is
--   $$
--   \mathrm{gft}_M(b,s):=\sum_{j=1}^m b_j\,x^B_j(b,s)-\sum_{\ell=1}^k s_\ell\,x^S_\ell(b,s),
--   $$
--   a real number that may be negative.
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), §2.1, p.10 (PDF 12)

import Mathlib
import Definitions.Def_RecruitSmaller_Supplement_Mechanism

namespace RecruitSmaller.Supplement

/-- The **realized expected Gains From Trade** of a mechanism under truthful reporting
(Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), §2.1, p.10): `gft_M(b, s) := ∑ⱼ b_j·xB_j(b, s) − ∑ₗ s_ℓ·xS_ℓ(b, s)`, a real number (it
may be negative). -/
noncomputable def gft {m k : ℕ} (M : Mechanism m k) (b : Fin m → ℝ) (s : Fin k → ℝ) : ℝ :=
  ∑ j, b j * M.xB j b s - ∑ l, s l * M.xS l b s

end RecruitSmaller.Supplement


