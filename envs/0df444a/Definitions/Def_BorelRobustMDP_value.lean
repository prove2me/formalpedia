-- Prove2me | Definitions.Def_BorelRobustMDP_value
-- name    : BorelRobustMDP_value
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:15:43.156701+00:00
-- url     : https://prove2.me/theorems/4cde9d00-8fab-4bba-8fdc-c0b4c476436c
-- title:
--   The values $V_{n\pi\gamma}$, $V_{n\pi}$ and $V_n$
-- statement:
--   For a policy pair $(\pi,\gamma)\in\Pi^R\times\Gamma$ and $h_n\in\mathcal H_n$:
--
--   $$V_{n\pi\gamma}(h_n)=\mathbb E^{\pi\gamma}_{nh_n}\Big[\sum_{k=n}^{N-1}c_k(X_k,A_k,X_{k+1})+c_N(X_N)\Big],\quad V_{n\pi}(h_n)=\sup_{\gamma\in\Gamma}V_{n\pi\gamma}(h_n),\quad V_n(h_n)=\inf_{\pi\in\Pi^R}\sup_{\gamma\in\Gamma}V_{n\pi\gamma}(h_n).$$
--
--   These are the objective of the controller, who minimizes the expected cost under the most adverse reaction of nature.
--
--   **Formalization Note.** $V_{n\pi\gamma}$ is an integral against the law of motion continuing $h_n$ to the horizon, not a recursion. The suprema and infima are real ones over the non-empty types of policies; at feasible histories they are bounded by Lemma 3.3.
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, (2.5), p.5, and p.8

import Mathlib
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BorelRobustMDP_Policy
import Definitions.Def_BorelRobustMDP_NaturePolicy
import Definitions.Def_BorelRobustMDP_pathLaw

open MeasureTheory
open MDPFinance.Bellman (Hist histState)

namespace BorelRobustMDP

universe u v

variable {E A : Type u} {Z : Type v} [MeasurableSpace E] [MeasurableSpace A] [MeasurableSpace Z]
  {N : ℕ}

/-- The law of the process after a history `h_n`, under `(π, γ)`, for `j` further transitions: the
conditional law `ℚ^{πγ}_x(· | H_n = h_n)` of (2.4) (Bäuerle & Glauner, arXiv:2007.13103v1, p.5). -/
noncomputable def law (R : RobustModel E A Z N) (π : Policy R.toDecisionModel)
    (γ : NaturePolicy R) (n : ℕ) (h : Hist E A n) (j : ℕ) : Measure (Hist E A (n + j)) :=
  pathLaw R n n (fun j => π.act (n + j)) (fun j => γ.act (n + j)) h j

/-- The value `V_{nπγ}(h_n)` of (2.5) (Bäuerle & Glauner, arXiv:2007.13103v1, p.5): the expected cost
from time `n` to the horizon `N` under the law of motion.

**Formalization Note.** `V` is an expectation, not a recursion; Proposition 3.5 is the recursion.
`N - n` is used for `n ≤ N`. The value is meaningful at feasible histories. -/
noncomputable def value (R : RobustModel E A Z N) (π : Policy R.toDecisionModel)
    (γ : NaturePolicy R) (n : ℕ) (h : Hist E A n) : ℝ :=
  ∫ h', totalCost R n n (N - n) h' ∂(law R π γ n h (N - n))

/-- The robust value `V_{nπ}(h_n) = sup_{γ∈Γ} V_{nπγ}(h_n)` of a policy (Bäuerle & Glauner,
arXiv:2007.13103v1, p.8).

**Formalization Note.** A real supremum over the non-empty type of policies of nature, bounded at
feasible histories by Lemma 3.3. -/
noncomputable def robustValue (R : RobustModel E A Z N) (π : Policy R.toDecisionModel) (n : ℕ)
    (h : Hist E A n) : ℝ :=
  ⨆ γ : NaturePolicy R, value R π γ n h

/-- The value function `V_n(h_n) = inf_{π∈Π^R} sup_{γ∈Γ} V_{nπγ}(h_n)` (Bäuerle & Glauner,
arXiv:2007.13103v1, p.5).

**Formalization Note.** A real infimum over the non-empty type of randomized policies, bounded at
feasible histories by Lemma 3.3. -/
noncomputable def optimalValue (R : RobustModel E A Z N) (n : ℕ) (h : Hist E A n) : ℝ :=
  ⨅ π : Policy R.toDecisionModel, robustValue R π n h

end BorelRobustMDP


