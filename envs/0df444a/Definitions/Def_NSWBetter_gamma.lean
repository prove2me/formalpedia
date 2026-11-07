-- Prove2me | Definitions.Def_NSWBetter_gamma
-- name    : NSWBetter_gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:48:38.064414+00:00
-- url     : https://prove2.me/theorems/e9611473-f2c4-44e0-95ec-f79ad6e58242
-- title:
--   The constant $\gamma=10^{-10}$
-- statement:
--   Throughout the paper $\gamma=10^{-10}$ (Section 2.3).
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 2.3, p.11

import Mathlib

namespace NSWBetter

/-- **The constant γ.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 2.3, p.11: "Throughout this paper, we will use γ to denote the value 10^−10." -/
noncomputable def gamma : ℝ := 1 / 10 ^ 10

end NSWBetter


