-- Prove2me | Definitions.Def_KashUpgrade_newCustomerChoice
-- name    : KashUpgrade_newCustomerChoice
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:20:55.705651+00:00
-- url     : https://prove2.me/theorems/3c7e60af-d4d3-45bb-b7b7-0bc57122b173
-- title:
--   The choice $q_1$ of a newly arriving customer
-- statement:
--   A newly arriving customer of type $\theta$ at time $t$ chooses her preferred class among the introduced ones:
--   $$
--   q_1(\pi,t,\theta)=\arg\max_{i\ \text{s.t.}\ s_i\le t}\ \theta\cdot s_i-x_{i,0} .
--   $$
--   In case of ties she chooses the latest class; in particular a new customer who is indifferent between opting out and buying will buy.
--
--   **Formalization Note** The largest maximizer is written as the supremum of the set of maximizers in $\mathbb N$. That set is finite and nonempty, since finitely many classes satisfy $s_i\le t$ and class $0$ is one of them.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), (2), p.10; p.11

import Mathlib
import Definitions.Def_KashUpgrade_IsIntroduced
import Definitions.Def_KashUpgrade_classPrice

namespace KashUpgrade

/-- **The choice of a newly arriving customer.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), (2), p.10:
`q₁(π, t, θ) = argmax_{i : s_i ≤ t} θ · s_i - x_{i,0}`. Ties go to the latest technology class,
so a new customer who is indifferent between opting out and buying buys (p.11).

**Formalization Note** The `sSup` in `ℕ` is the largest maximizer: the set of classes with
`s_i ≤ t` is finite and contains class `0`, so the set of maximizers is finite and nonempty. -/
noncomputable def newCustomerChoice (S : Schedule) (x : ℕ → ℕ → ℝ) (t : ℕ) (θ : ℝ) : ℕ :=
  sSup {i | IsIntroduced S i ∧ S.s i ≤ t ∧
    ∀ i', IsIntroduced S i' → S.s i' ≤ t →
      θ * S.s i' - classPrice x i' 0 ≤ θ * S.s i - classPrice x i 0}

end KashUpgrade


