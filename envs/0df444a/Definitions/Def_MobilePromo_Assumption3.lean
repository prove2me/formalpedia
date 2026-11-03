-- Prove2me | Definitions.Def_MobilePromo_Assumption3
-- name    : MobilePromo_Assumption3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:45.948187+00:00
-- url     : https://prove2.me/theorems/37206146-88c3-406e-bafa-f44b92e31998
-- title:
--   Assumption 3: optimal bids are interior
-- statement:
--   For the first $I$ seasons, for all locations $l$, all $\gamma\in\Gamma^{(0)}$, all $1\le t\le T$ and all states with $\mathcal F\ne\emptyset$,
--
--   $$
--   b^*_{i,t,l}(\boldsymbol c_i;\gamma)\in(b^{\min},b^{\max}),
--   $$
--
--   the interior of the bidding interval. It makes the optimal bids differentiable in the marginal value and the parameter, which is what Lemma 1 needs.
--
--   **Formalization Note** The states are $\boldsymbol c\le\boldsymbol W$, the state space $c_{i,t,j}\in\{0,\dots,W_{i,j}\}$ of p.8.
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, Assumption 3, p.14; state space, p.8

import Mathlib
import Definitions.Def_MobilePromo_V

set_option autoImplicit false

namespace MobilePromo

/-- Assumption 3 for the first `I` seasons (SSRN 3523491, Assumption 3, p.14): for all `l`,
`γ ∈ Γ⁽⁰⁾`, `F ≠ ∅`, `1 ≤ i ≤ I` and `1 ≤ t ≤ T`, the optimal bid lies in the interior of `B`.

**Formalization Note** Seasons are `i < I` (0-based). The states are `c ≤ W`, the state space
`c_{i,t,j} ∈ {0, …, W_{i,j}}` of p.8. -/
def Assumption3 (M : Model) {T : ℕ} (S : Schedule T) (I : ℕ) : Prop :=
  ∀ i < I, ∀ t, 1 ≤ t → t ≤ T → ∀ c : Fin (S i).m → ℕ, c ≤ (S i).W →
    ((S i).activeSet t c).Nonempty → ∀ l, ∀ γ ∈ M.Gamma0,
      M.bmin < bStar M (S i) γ t c l ∧ bStar M (S i) γ t c l < M.bmax

end MobilePromo


