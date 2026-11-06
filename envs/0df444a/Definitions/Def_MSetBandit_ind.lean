-- Prove2me | Definitions.Def_MSetBandit_ind
-- name    : MSetBandit_ind
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:40.495198+00:00
-- url     : https://prove2.me/theorems/8568a50f-5274-4955-b20d-dedf3a1160f2
-- title:
--   Indicator vector $\mathbf 1_S$ of an action
-- statement:
--   For an action $S\in\mathcal X_{d,m}$, its **indicator vector** $\mathbf 1_S\in\mathbb R^d$ has $i$-th coordinate $1$ if item $i$ is selected ($i\in S$) and $0$ otherwise. The inner product $x^\top\ell$ of an action $x=\mathbf 1_S$ with a loss vector $\ell\in\mathbb R^d$ is the total loss $\sum_{i\in S}\ell_i$ of the selected items.
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Section 2, p.3

import Mathlib
import Definitions.Def_MSetBandit_Action

namespace MSetBandit

/-- **Indicator vector `1_S` of an action.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Section 2, p.3: "each m-set `S ⊆ [d]`
corresponds to the indicator vector `1_S ∈ X`", with `x_i = 1` if item `i` is selected and `x_i = 0`
otherwise.

**Formalization Note.** Vectors of `ℝ^d` are functions `Fin d → ℝ`; `ind x ⬝ᵥ ℓ` is the inner
product `x^⊤ℓ`. -/
def ind {d m : ℕ} (x : Action d m) : Fin d → ℝ :=
  fun i => if i ∈ x.1 then 1 else 0

end MSetBandit


