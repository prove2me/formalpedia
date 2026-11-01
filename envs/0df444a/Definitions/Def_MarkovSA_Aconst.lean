-- Prove2me | Definitions.Def_MarkovSA_Aconst
-- name    : MarkovSA_Aconst
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:14.520461+00:00
-- url     : https://prove2.me/theorems/b606ce97-8834-4fbf-be9b-1177dab21fd3
-- title:
--   $A=A_1+A_2+1$
-- statement:
--   The combined effective Lipschitz constant $A=A_1+A_2+1$.
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, §2.2, p.6

import Mathlib

namespace MarkovSA

/-- `A = A₁ + A₂ + 1`, the combined effective Lipschitz constant (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, §2.2, p.6). -/
def Aconst (A₁ A₂ : ℝ) : ℝ := A₁ + A₂ + 1

end MarkovSA


