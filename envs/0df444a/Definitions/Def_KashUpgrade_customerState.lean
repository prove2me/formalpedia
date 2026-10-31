-- Prove2me | Definitions.Def_KashUpgrade_customerState
-- name    : KashUpgrade_customerState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:21:57.137583+00:00
-- url     : https://prove2.me/theorems/b30f892f-27c3-4389-a3cf-c7018142ef98
-- title:
--   The choice $q_\ell$ and upgrade experience $m_\ell$ of a customer
-- statement:
--   For a customer of type $\theta$ in her $\ell$-th period at time $t$, the pair $(q_\ell(\pi,t,\theta),m_\ell(\pi,t,\theta))$ is defined by recursion on $\ell$. For $\ell=1$ it is $(q_1(\pi,t,\theta),0)$. For $2\le\ell$, write $(q,m)=(q_{\ell-1}(\pi,t-1,\theta),m_{\ell-1}(\pi,t-1,\theta))$. Then:
--
--   1. if $t\le s_1$, the choice is class $0$;
--   2. if $t>s_1$, class $q+1$ exists, $s_{q+1}=t$, and
--   $$
--   \theta\cdot s_q-x_{q,m}\le\theta\cdot s_{q+1}-x_{q+1,m+1}-c,
--   $$
--   the pair is $(q+1,m+1)$;
--   3. otherwise the pair is $(q,m)$.
--
--   The customer is myopic, and $c>0$ is the switching cost. The only upgrade offered is the one of Assumption 1, from the previous class to the current one, at the time of its introduction.
--
--   **Formalization Note** The sequences (3) and (4) are one recursion returning the pair. The paper prints $m_\ell$ only for $t\ge s_1$; before that the price is $0$ whatever $m_\ell$ is, and the pair is $(0,0)$. The index $\ell$ is 1-based as in the paper, and $\ell=0$ is unused.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), (3)–(4), p.11; Assumption 1, p.10

import Mathlib
import Definitions.Def_KashUpgrade_newCustomerChoice
open Classical

namespace KashUpgrade

/-- **The class and the upgrade experience of a customer.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), (3)–(4), p.11:
`customerState S x c ℓ t θ = (q_ℓ(π, t, θ), m_ℓ(π, t, θ))` for a customer of type `θ` in her `ℓ`-th
period at time `t`. An existing customer stays with her previous choice, or at the introduction time
of the next class pays the switching cost `c` to adopt it, on `≤` (ties go to the latest class).

**Formalization Note** `ℓ` is 1-based as in the paper, and `ℓ = 0` is unused. The two sequences of
(3) and (4) are one recursion on `ℓ` returning the pair. The experience `m_ℓ` is printed only for
`t ≥ s₁`; before that `q_ℓ = 0` and the price is `0` whatever `m_ℓ` is, and the pair is `(0, 0)`.
The clause `s_{q+1} = t` also requires that class `q + 1` exists, which is what a finite schedule
means. Assumption 1 is built in: the only upgrade offered is from class `q` to class `q + 1`, at the
time of its introduction. -/
noncomputable def customerState (S : Schedule) (x : ℕ → ℕ → ℝ) (c : ℝ) :
    ℕ → ℕ → ℝ → ℕ × ℕ
  | 0, _, _ => (0, 0)
  | 1, t, θ => (newCustomerChoice S x t θ, 0)
  | ℓ + 2, t, θ =>
    if t ≤ S.s 1 then (0, 0) else
      let prev := customerState S x c (ℓ + 1) (t - 1) θ
      if IsIntroduced S (prev.1 + 1) ∧ S.s (prev.1 + 1) = t ∧
          θ * S.s prev.1 - classPrice x prev.1 prev.2 ≤
            θ * S.s (prev.1 + 1) - classPrice x (prev.1 + 1) (prev.2 + 1) - c then
        (prev.1 + 1, prev.2 + 1)
      else prev

end KashUpgrade


