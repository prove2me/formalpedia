-- Prove2me | Definitions.Def_MarkovSA_Bconst
-- name    : MarkovSA_Bconst
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:16.859009+00:00
-- url     : https://prove2.me/theorems/31e23497-3fc6-4d01-a69b-f047c2528187
-- title:
--   $B=B_1+B_2$
-- statement:
--   The combined constant $B=B_1+B_2$.
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, §2.2, p.6

import Mathlib

namespace MarkovSA

/-- `B = B₁ + B₂` (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, §2.2, p.6). -/
def Bconst (B₁ B₂ : ℝ) : ℝ := B₁ + B₂

end MarkovSA


