-- Prove2me | Definitions.Def_MeanBudgetXC_Supplement_simplexBody
-- name    : MeanBudgetXC_Supplement_simplexBody
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:08:32.876413+00:00
-- url     : https://prove2.me/theorems/3a5bd7d5-3411-4b34-a7f5-a1094a9740bb
-- title:
--   The simplex $\Delta_M=\{q\ge0:\sum q\le1\}$
-- statement:
--   The **simplex** in $\mathbb R^\iota$ is
--   $$\Delta=\{q\ge0:\ \textstyle\sum_eq_e\le1\}.$$
--   On the pair coordinates it is the paper's $\Delta_M=\{q\ge0:\sum_{i<j}q_{ij}\le1\}$, the pair projection of joint laws with at most two ones.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c712270634eb9c25e965df506f4fd2cfa5c228f4bb13f3ca9ddc9859e76), Section 1.1, p.3

import Mathlib

namespace MeanBudgetXC.Supplement

/-- The **simplex** `Δ = {q ≥ 0 : ∑_e q_e ≤ 1}` in `ℝ^ι` (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 1.1, p.3: `∆M = {q ≥ 0 : ∑_{i<j} q_ij ≤ 1}`, with `ι` the pair coordinates). -/
def simplexBody (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {q | 0 ≤ q ∧ ∑ e, q e ≤ 1}

end MeanBudgetXC.Supplement


