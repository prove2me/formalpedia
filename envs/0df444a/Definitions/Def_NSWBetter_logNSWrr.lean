-- Prove2me | Definitions.Def_NSWBetter_logNSWrr
-- name    : NSWBetter_logNSWrr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:59.826983+00:00
-- url     : https://prove2.me/theorems/d468de3c-7068-4a1a-813e-985f7e3de5e8
-- title:
--   Log Nash welfare $\mathrm{logNSW}(W)$ of the round robin allocation
-- statement:
--   The log Nash welfare of the round robin allocation $W$ of an instance with $\Delta$ identical agents and value multiset $s$:
--   $$\mathrm{logNSW}(W)=\frac1\Delta\sum_{i=1}^{\Delta}\ln v(W_i)\in[-\infty,\infty),$$
--   with $\ln 0=-\infty$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 2, p.9 (logNSW); Section 3, p.11 (W)

import Mathlib
import Definitions.Def_HayashiHoeffding_elog
import Definitions.Def_NSWBetter_rrBundle

namespace NSWBetter

/-- **Log Nash welfare of the round-robin allocation.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 2, p.9: "logNSW(X) … (1/n) Σ ln(vi(Xi))"; Section 3, p.11: the round robin allocation `W`.

`logNSWrr Δ s = (1/Δ) Σ_(i < Δ) HayashiHoeffding.elog(v(W_i))` in `EReal`: `−∞` as soon as one bundle has value `0`. -/
noncomputable def logNSWrr (Δ : ℕ) (s : Multiset ℝ) : EReal :=
  ((1 / Δ : ℝ) : EReal) * ∑ i : Fin Δ, HayashiHoeffding.elog (rrBundle Δ s i)

end NSWBetter


