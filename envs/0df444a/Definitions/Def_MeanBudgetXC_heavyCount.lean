-- Prove2me | Definitions.Def_MeanBudgetXC_heavyCount
-- name    : MeanBudgetXC_heavyCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:38:38.97049+00:00
-- url     : https://prove2.me/theorems/50bae2b9-69d9-438e-baf8-976eb3d435a6
-- title:
--   The number of heavy edges $m_{\mathrm{heavy}}$
-- statement:
--   The **number of heavy edges** of the host graph is
--   $$m_{\mathrm{heavy}}=6n_0+\ell|E(T)|+c.$$
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 4.3, p.19

import Mathlib

namespace MeanBudgetXC

/-- The number of heavy edges `m_heavy = 6 n₀ + ℓ |E(T)| + c` (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 4.3, p.19). -/
def heavyCount (n₀ ℓ c : ℕ) {t : ℕ} (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] : ℕ :=
  6 * n₀ + ℓ * T.edgeFinset.card + c

end MeanBudgetXC


