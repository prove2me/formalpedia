-- Prove2me | Definitions.Def_MSetBandit_Plam
-- name    : MSetBandit_Plam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:41:03.541361+00:00
-- url     : https://prove2.me/theorems/8eb744c3-960e-48b4-8d1e-0182a81b9538
-- title:
--   The smoothed set $\mathcal P_\lambda$
-- statement:
--   Let $r=m/d$. For a real number $\lambda$, the set $\mathcal P_\lambda$ consists of the distributions whose marginals stay away from $0$ and $1$:
--   $$
--   \mathcal P_\lambda=\{p\in\Delta(\mathcal X):\ \lambda r\le\mu_i(p)\le1-\lambda(1-r)\ \text{for every }i\in[d]\}.
--   $$
--   The uniform distribution has $\mu_i(U)=r$ and lies in $\mathcal P_\lambda$ for every $\lambda\in(0,1)$.
--
--   **Formalization Note** The paper fixes $\lambda\in(0,1)$ when defining the set; here it is defined for every real $\lambda$ and each theorem states the range it uses (Algorithm 1 uses $\lambda$ and $\lambda/2$ with $\lambda\le1/2$).
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Section 2, Eq. (3), p.4

import Mathlib
import Definitions.Def_MSetBandit_IsDist
import Definitions.Def_MSetBandit_marg

namespace MSetBandit

/-- **The smoothed set `P_λ`.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Section 2, Eq. (3), p.4: with `r := m/d`,
`P_λ := {p ∈ ∆(X) : λr ≤ µ_i(p) ≤ 1 − λ(1 − r) for every i ∈ [d]}`.

**Formalization Note.** The page fixes `λ ∈ (0, 1)`; the set is defined here for every real `λ`,
and each theorem states the range of `λ` it uses (Lemma 7 takes `0 < λ ≤ 1/2`, the algorithm uses
`λ` and `λ/2`). `r` is the real number `(m : ℝ) / d`. -/
def Plam {d m : ℕ} (lam : ℝ) : Set (Action d m → ℝ) :=
  {p | IsDist p ∧ ∀ i, lam * ((m : ℝ) / d) ≤ marg p i ∧ marg p i ≤ 1 - lam * (1 - (m : ℝ) / d)}

end MSetBandit


