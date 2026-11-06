-- Prove2me | Definitions.Def_IAFTRL_IsMin2_3
-- name    : IAFTRL_IsMin2_3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:47:56.14155+00:00
-- url     : https://prove2.me/theorems/e8ce98c9-c72d-4ca6-9712-c568baad2bbd
-- title:
--   Minimizers of the sampling program (2.3)
-- statement:
--   For round $t\ge1$ and cumulative estimate $S$, a distribution $p$ **solves (2.3)** if it is feasible for (2.3) and minimizes the empirical exploration cost over the feasible set:
--   $$
--   \sum_ap_a\hat\Delta_t(a)\le\sum_ap'_a\hat\Delta_t(a)\qquad\text{for every feasible }p' .
--   $$
--   This is the objective (2.3a). IA-FTRL samples its action from such a $p_t$, chosen by a fixed history-measurable rule when the minimizer is not unique.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Section 2.1, pp.17–18, Eq. (2.3a)

import Mathlib
import Definitions.Def_IAFTRL_gapHat
import Definitions.Def_IAFTRL_IsFeasible2_3

namespace IAFTRL

/-- **Minimizers of program (2.3).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Section 2.1, p.18, Eq. (2.3a): "minimize over
`p ∈ 𝒫(𝒜)` `Σ_a p_a Δ̂_t(a)`" subject to (2.3b)–(2.3f).

`IsMin2_3 arms t S p` says that `p` is feasible for (2.3) (`IsFeasible2_3`) and that its empirical
exploration cost `⟨p, Δ̂_t⟩` is at most that of every feasible `p'` (paper round `t ≥ 1`,
`S = Σ_{s<t} θ̂_s`). -/
def IsMin2_3 {d K : ℕ} (arms : Fin K → Fin d → ℝ) (t : ℕ) (S : Fin d → ℝ)
    (p : Fin K → ℝ) : Prop :=
  IsFeasible2_3 arms t S p ∧
    ∀ p' : Fin K → ℝ, IsFeasible2_3 arms t S p' →
      ∑ a, p a * gapHat arms t S a ≤ ∑ a, p' a * gapHat arms t S a

end IAFTRL


