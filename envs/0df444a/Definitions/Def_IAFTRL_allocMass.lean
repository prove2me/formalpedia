-- Prove2me | Definitions.Def_IAFTRL_allocMass
-- name    : IAFTRL_allocMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:38.913105+00:00
-- url     : https://prove2.me/theorems/8b67c9e7-0fd9-401a-94a2-f787eab04a8c
-- title:
--   Total mass $N_n$ of an allocation
-- statement:
--   The **total mass** of an allocation $n\in\mathbb R^{\mathcal A}$ is
--   $$
--   N_n=\sum_{a\in\mathcal A}n_a .
--   $$
--   Lemma C.3 bounds the mass of an allocation whose cost is at most $2c^*$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Appendix D.1, pp.63–64

import Mathlib

namespace IAFTRL

/-- **Total mass `N_n` of an allocation.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Appendix D.1.1, p.64: "total mass
`N_n = Σ_a n_a` of a fixed feasible sampling allocation" (also p.63).

`allocMass n = Σ_j n_j`. -/
def allocMass {K : ℕ} (n : Fin K → ℝ) : ℝ :=
  ∑ j, n j

end IAFTRL


