-- Prove2me | Definitions.Def_MSetBandit_expect
-- name    : MSetBandit_expect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:55.010673+00:00
-- url     : https://prove2.me/theorems/46d2bbec-66a7-475f-bf0a-a5e373bbd0ad
-- title:
--   Expectation $\mathbb E_{X\sim p}[f(X)]$ over actions
-- statement:
--   For a function $p:\mathcal X\to\mathbb R$ (typically a distribution in $\Delta(\mathcal X)$) and $f:\mathcal X\to\mathbb R$,
--   $$
--   \mathbb E_{X\sim p}[f(X)]=\sum_{x\in\mathcal X}p(x)\,f(x).
--   $$
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Section 2, p.4

import Mathlib
import Definitions.Def_MSetBandit_Action

namespace MSetBandit

/-- **Expectation `E_{X∼p}[f(X)]` under a distribution on actions.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Section 2, p.4
(`E_{X∼p}`), a finite sum over the action set: `E_{X∼p}[f(X)] = Σ_{x∈X} p(x) f(x)`. -/
def expect {d m : ℕ} (p : Action d m → ℝ) (f : Action d m → ℝ) : ℝ :=
  ∑ x, p x * f x

end MSetBandit


