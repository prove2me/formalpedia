-- Prove2me | Definitions.Def_PrizeAlloc_SingleParam_Strengthenings
-- name    : PrizeAlloc_SingleParam_Strengthenings
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:54.193545+00:00
-- url     : https://prove2.me/theorems/cae1ea60-de36-4e8a-a35f-7bb453a9ea10
-- title:
--   p. 19 — geometric rules
-- statement:
--   Geometric rules (p. 19), the family of Corollary 6. A prize allocation rule $\varphi$ is a **geometric rule** if there is $\lambda\in[0,1]$ such that for each competition $(N,\mathcal R,E)$ and each $i\in N$
--   $$\varphi_i(N,\mathcal R,E)=\frac{\lambda^{\mathcal R(i)-1}}{\sum_{k=1}^{|N|}\lambda^{k-1}}\,E,$$
--   with $\lambda^0=1$ for each $\lambda\in[0,1]$ (footnote 10). The strengthened axioms used by Corollaries 5 and 6 (strict and winner-loser strict order preservation, strict endowment monotonicity, endowment additivity) are the shared definitions in `PrizeAlloc.Interval.Companions`.
--
--   **Formalization Note** Same encoding of competitions as in the shared Setting; the condition is required for every ranking and every $E\ge 0$. The parameter $\lambda$ is named `c` in Lean (`λ` is reserved). Lean's convention $0^0=1$ is footnote 10's. The denominator is at least $1$ (its first term is $\lambda^0=1$), so the division is never by zero.
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, p. 19, Geometric rules (footnote 10)

import Mathlib
import Definitions.Def_PrizeAlloc_SingleParam_Setting
import Definitions.Def_PrizeAlloc_Interval_Companions

namespace PrizeAlloc.SingleParam

variable {U : Type*} [DecidableEq U]

/-- Geometric rules (p. 19): there is `λ ∈ [0, 1]` with
`φ_i(N, R, E) = λ^{R(i)-1} / (∑_{k=1}^{|N|} λ^{k-1}) · E` (and `λ^0 = 1`, footnote 10). -/
def IsGeometricRule (φ : List U → ℝ → U → ℝ) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ l E, PrizeAlloc.Interval.IsRanking l → 0 ≤ E → ∀ i ∈ l,
    φ l E i = c ^ (PrizeAlloc.Interval.pos l i - 1) / (∑ k ∈ Finset.range l.length, c ^ k) * E

end PrizeAlloc.SingleParam


