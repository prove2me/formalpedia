-- Prove2me | Definitions.Def_MatchedUCLB_objDelta
-- name    : MatchedUCLB_objDelta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:34:29.785378+00:00
-- url     : https://prove2.me/theorems/bdcd006b-1bb8-4e88-a569-160fa132447b
-- title:
--   The smoothing widths $\delta_j=c_1\lambda m\tau_j^q$
-- statement:
--   The **smoothing widths** of the complete objective are $\delta_j=c_1\lambda m\tau_j^q$, with $\lambda=K\mu m^{a_q}$, $\tau_j=\eta^j\tau_0$ and $c_1=2^{-q-3}/q$. They are the prefix gaps of Lemma 4.5(c) up to the factor $7$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Lemma 4.5(c), p.10

import Mathlib
import Definitions.Def_MatchedUCLB_objLam
import Definitions.Def_MatchedUCLB_objTau
import Definitions.Def_MatchedUCLB_deltaC

namespace MatchedUCLB

/-- **The smoothing widths `δ_j = c_1λmτ_j^q` of the complete objective.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Lemma 4.5(c),
p.10. -/
noncomputable def objDelta (q μ : ℝ) (m : ℕ) (τ₀ : ℝ) (j : ℕ) : ℝ :=
  deltaC q m (objLam q μ m) (objTau q τ₀ j)

end MatchedUCLB


