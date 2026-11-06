-- Prove2me | Definitions.Def_MSetBandit_IsDist
-- name    : MSetBandit_IsDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:45.650477+00:00
-- url     : https://prove2.me/theorems/f06f6487-e914-47e8-8e83-da8d5c07e358
-- title:
--   The probability simplex $\Delta(\mathcal X)$
-- statement:
--   A function $p:\mathcal X\to\mathbb R$ belongs to the **probability simplex**
--   $$
--   \Delta(\mathcal X)=\Big\{p:\mathcal X\to[0,1]:\ \sum_{x\in\mathcal X}p(x)=1\Big\}
--   $$
--   if every value $p(x)$ lies in $[0,1]$ and the values sum to one.
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Section 2, p.3

import Mathlib
import Definitions.Def_MSetBandit_Action

namespace MSetBandit

/-- **The probability simplex `∆(X)`.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Section 2, p.3:
`∆(X) := {p : X → [0, 1] : Σ_{x∈X} p(x) = 1}`.

`IsDist p` says that `p` takes values in `[0, 1]` and sums to one over the actions. -/
def IsDist {d m : ℕ} (p : Action d m → ℝ) : Prop :=
  (∀ x, 0 ≤ p x ∧ p x ≤ 1) ∧ ∑ x, p x = 1

end MSetBandit


