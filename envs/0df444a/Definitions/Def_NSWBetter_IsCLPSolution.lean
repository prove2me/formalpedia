-- Prove2me | Definitions.Def_NSWBetter_IsCLPSolution
-- name    : NSWBetter_IsCLPSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:11.368935+00:00
-- url     : https://prove2.me/theorems/a9ff3d30-7247-42ba-b940-5331afec465f
-- title:
--   Configuration LP solution (rational, valid, finite objective)
-- statement:
--   Following the paper's convention (p.19), a **configuration LP solution** is a rational, valid solution of (2)–(4) with a well-defined objective value.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 4.2, p.19 ("Every time we mention a configuration LP solution y …")

import Mathlib
import Definitions.Def_NSWBetter_IsValidCLP
import Definitions.Def_NSWBetter_FiniteObj
import Definitions.Def_NSWBetter_IsRationalCLP

namespace NSWBetter

/-- **Configuration LP solution, in the paper's standing sense.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 4.2, p.19: "Every time we mention a configuration LP solution y, we mean a rational configuration LP solution with a well-defined objective value."

`IsCLPSolution v y = IsValidCLP y ∧ FiniteObj v y ∧ IsRationalCLP y`. -/
def IsCLPSolution {n m : ℕ} (v : Fin n → Fin m → ℝ) (y : Fin n → Finset (Fin m) → ℝ) : Prop :=
  IsValidCLP y ∧ FiniteObj v y ∧ IsRationalCLP y

end NSWBetter


