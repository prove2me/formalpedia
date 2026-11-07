-- Prove2me | Definitions.Def_NSWBetter_IsRationalCLP
-- name    : NSWBetter_IsRationalCLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:32.997105+00:00
-- url     : https://prove2.me/theorems/31fcf116-7c12-4691-a63a-8dcaaece95d9
-- title:
--   Rational configuration LP solution
-- statement:
--   Every entry $y_{i,S}$ of the configuration LP solution is a rational number.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 4.1, p.17; Section 4.2, p.19

import Mathlib

namespace NSWBetter

/-- **Rational solution.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 4.1, p.17: "Throughout this paper, we only work with rational configuration LP solutions". -/
def IsRationalCLP {n m : ℕ} (y : Fin n → Finset (Fin m) → ℝ) : Prop :=
  ∀ i S, ∃ q : ℚ, y i S = q

end NSWBetter


