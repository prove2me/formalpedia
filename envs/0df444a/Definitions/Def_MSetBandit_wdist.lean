-- Prove2me | Definitions.Def_MSetBandit_wdist
-- name    : MSetBandit_wdist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:39.450881+00:00
-- url     : https://prove2.me/theorems/85671f05-18c6-4abb-907b-69433aacd3ef
-- title:
--   Weighted $m$-set distribution $p_\theta$
-- statement:
--   Given $\theta\in\mathbb R^d$, the **weighted $m$-set distribution** $p_\theta$ assigns to every $m$-set $S\subseteq[d]$ the probability
--   $$
--   p_\theta(S)=\frac{\exp\big(\sum_{i\in S}\theta_i\big)}{\sum_{A\subseteq[d]:\,|A|=m}\exp\big(\sum_{i\in A}\theta_i\big)},
--   $$
--   so $p_\theta(S)\propto e^{\theta^\top\mathbf 1_S}$. It is described by the $d$ parameters $\theta_1,\dots,\theta_d$ although it may charge exponentially many actions; it is also known as a conditional Bernoulli distribution.
--
--   **Formalization Note** The denominator is a sum over the finite action type, which is nonempty in every theorem (all assume $1\le m\le d-1$).
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Section 2, p.4

import Mathlib
import Definitions.Def_MSetBandit_ind
open Matrix

namespace MSetBandit

/-- **The weighted m-set distribution `p_θ`.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Section 2, p.4: for `θ ∈ ℝ^d` and every
m-set `S`,
`p_θ(S) := exp(Σ_{i∈S} θ_i) / Σ_{A⊆[d], |A|=m} exp(Σ_{i∈A} θ_i)`, so `p_θ(S) ∝ e^{θ^⊤ 1_S}`.

**Formalization Note.** `θ ⬝ᵥ ind x = Σ_{i∈S} θ_i` for the action `x = S`. The type of actions is
nonempty whenever `m ≤ d`, so the denominator is positive in every theorem that uses `wdist`
(all of them assume `1 ≤ m`, `m + 1 ≤ d`). -/
noncomputable def wdist {d m : ℕ} (θ : Fin d → ℝ) : Action d m → ℝ :=
  fun x => Real.exp (θ ⬝ᵥ ind x) / ∑ y : Action d m, Real.exp (θ ⬝ᵥ ind y)

end MSetBandit


