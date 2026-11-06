-- Prove2me | Definitions.Def_MSetBandit_regret
-- name    : MSetBandit_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:51.847303+00:00
-- url     : https://prove2.me/theorems/4d8a3c3e-f066-4297-afb6-052ba55533af
-- title:
--   Realized regret $R_T$
-- statement:
--   For losses $\ell_1,\dots,\ell_T$ and played actions $X_1,\dots,X_T$, the **realized regret** against the best fixed action in hindsight is
--   $$
--   R_T=\sum_{t=1}^TX_t^\top\ell_t-\min_{x\in\mathcal X}\sum_{t=1}^Tx^\top\ell_t .
--   $$
--   Under an adaptive adversary the comparator may depend on the realized history.
--
--   **Formalization Note** Rounds are indexed from $0$. The minimum over the finite, nonempty action set is written as an infimum.
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Section 2, Eq. (4), p.4

import Mathlib
import Definitions.Def_MSetBandit_ind
open Matrix

namespace MSetBandit

/-- **Realized regret `R_T` of (4).** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Section 2, Eq. (4), p.4:
`R_T := Σ_{t=1}^T X_t^⊤ ℓ_t − min_{x∈X} Σ_{t=1}^T x^⊤ ℓ_t`, against the best fixed action in
hindsight (which may depend on the realized history).

**Formalization Note.** Rounds are 0-based (`t = 0, …, T − 1`). The minimum over the finite
action type is `⨅`; for `m ≤ d` the type is nonempty and the infimum is the attained minimum. -/
noncomputable def regret {d m : ℕ} (T : ℕ) (ℓ : ℕ → Fin d → ℝ) (X : ℕ → Action d m) : ℝ :=
  ∑ t ∈ Finset.range T, ind (X t) ⬝ᵥ ℓ t - ⨅ x : Action d m, ∑ t ∈ Finset.range T, ind x ⬝ᵥ ℓ t

end MSetBandit


