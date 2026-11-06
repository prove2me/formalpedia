-- Prove2me | Definitions.Def_MatchedUCLB_objLam
-- name    : MatchedUCLB_objLam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:35.089864+00:00
-- url     : https://prove2.me/theorems/b15e4573-928c-45d7-9d57-1c8cef203a32
-- title:
--   The chain coefficient $\lambda=K\mu m^{a_q}$
-- statement:
--   For $\mu>0$ and a chain length $m$, the **chain coefficient** of the complete objective is $\lambda=K\mu m^{a_q}$, with $K=5^{(q-1)/2}/c_0$ and $a_q=(3q-2)/2$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eq. (4.15), p.9; Lemma 4.5, p.10

import Mathlib
import Definitions.Def_MatchedUCLB_KConst
import Definitions.Def_MatchedUCLB_aQ

namespace MatchedUCLB

/-- **The chain coefficient `λ = Kμm^{a_q}`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Eq. (4.15), p.9, with
`K = 5^{(q−1)/2}/c_0` (Lemma 4.5, p.10). -/
noncomputable def objLam (q μ : ℝ) (m : ℕ) : ℝ :=
  KConst q * μ * (m : ℝ) ^ aQ q

end MatchedUCLB


