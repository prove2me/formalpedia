-- Prove2me | Definitions.Def_MSetBandit_Supplement_ActionLossesIn01
-- name    : MSetBandit_Supplement_ActionLossesIn01
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:46:51.950239+00:00
-- url     : https://prove2.me/theorems/9bfc5625-2ac0-4a6e-b152-8b8bb5dd6870
-- title:
--   Action losses in $[0,1]$ up to horizon $T$
-- statement:
--   An adversary $(f_t)$ has **action losses in $[0,1]$** up to horizon $T$ if
--   $$
--   0\le x^\top f_t(H)\le 1\qquad\text{for every round } t\le T,\ \text{every history } H \text{ of length } t-1,\ \text{and every action } x\in\mathcal X_{d,m}.
--   $$
--
--   This is the loss normalization of the paper's lower bounds (Theorems 2 and 3), in contrast to the $[-1,1]$ normalization of the upper bound.
--
--   **Formalization Note** Rounds are indexed from $0$ ($t<T$). The condition is imposed on every history, including histories that never arise; since an adversary may be redefined arbitrarily (for instance as $0$) on such histories, this is equivalent to requiring it along the interaction.
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Theorem 2, p.15; Theorem 3, p.40; Lemma 11, p.41

import Mathlib
import Definitions.Def_MSetBandit_ind
import Definitions.Def_MSetBandit_Supplement_DetAdversary
open Matrix

namespace MSetBandit.Supplement

/-- **Action losses in `[0,1]`.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Theorems 2 and 3, pp.15, 40, and Lemma 11, p.41:
"an adaptive non-anticipating adversary whose action losses belong to `[0, 1]` at every round",
i.e. `x^⊤ℓ_t ∈ [0,1]` for every action `x ∈ X_{d,m}` and every round `t ∈ [T]`.

`ActionLossesIn01 T adv` says: for every round `t < T`, every history `H` of length `t` and
every action `x`, `0 ≤ 1_x^⊤ f_t(H) ≤ 1`.

**Formalization Note.** Rounds are 0-based. The condition is imposed on every history, reachable
or not; this changes nothing, since an adversary can be redefined arbitrarily (e.g. as `0`) on
histories that never occur. -/
def ActionLossesIn01 {d m : ℕ} (T : ℕ) (adv : DetAdversary d m) : Prop :=
  ∀ t < T, ∀ (H : History d m t) (x : Action d m),
    0 ≤ ind x ⬝ᵥ adv.f t H ∧ ind x ⬝ᵥ adv.f t H ≤ 1

end MSetBandit.Supplement


