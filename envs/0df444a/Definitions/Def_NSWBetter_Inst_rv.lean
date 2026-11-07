-- Prove2me | Definitions.Def_NSWBetter_Inst_rv
-- name    : NSWBetter_Inst_rv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:08.115098+00:00
-- url     : https://prove2.me/theorems/f8c2567c-4290-40b1-ad30-9b07b114f6f7
-- title:
--   Real-valued valuations of a rational instance
-- statement:
--   For a rational instance $I$, $I.\mathrm{rv}$ is the real-valued valuation matrix $(v_i(g))_{i,g}$ obtained by casting each rational value to $\mathbb R$.
--
--   It lets the notions defined for real valuations (configuration LP, fractional allocations, ST rounding) be applied to an algorithm's rational input.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 2, p.8

import Mathlib
import Definitions.Def_NSWBetter_Inst

namespace NSWBetter

/-- **The valuations of a rational instance as real numbers.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 2, p.8: "vi : 2G → R≥0".

`I.rv i g = (I.v i g : ℝ)`, the values of `I` cast to the reals, so that the real-valued notions of Sections 3–6 apply to `I`. -/
noncomputable def Inst.rv (I : Inst) : Fin I.n → Fin I.m → ℝ := fun i g => ((I.v i g : ℚ) : ℝ)

end NSWBetter


