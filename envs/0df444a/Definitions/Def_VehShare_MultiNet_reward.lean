-- Prove2me | Definitions.Def_VehShare_MultiNet_reward
-- name    : VehShare_MultiNet_reward
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:40:56.069979+00:00
-- url     : https://prove2.me/theorems/6310e7f7-0f61-46bc-84b8-76cfc25fee5b
-- title:
--   Expected reward per unit time $R(q)$ (eq. (1))
-- statement:
--   For a policy $q$ and a stationary distribution $\pi$ of its chain, the **expected reward per unit time** is (eq. (1), p. 5)
--
--   $$
--   R(q)=\sum_{x\in S}\pi(x)\sum_{(i,j)\in\mathcal A}\Lambda_{ij}q_{ij}(x)I_{ij}(q_{ij}(x)).
--   $$
--
--   **Formalization Note** The distribution $\pi$ is an argument, since a policy may have several stationary distributions.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, eq. (1), p. 5

import Mathlib
import Definitions.Def_VehShare_MultiNet_Policy

namespace VehShare.MultiNet

/-- **Expected reward per unit time `R(q)`, eq. (1).**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), eq. (1), p. 5: `R(q) = ∑_{x∈S} π(x) ∑_{(i,j)∈𝒜} Λ_ij q_ij(x) I_ij(q_ij(x))`.

The distribution `π` is an argument (Reading 2: a policy may have several stationary laws).
Pairs with `Λ_ij = 0` contribute 0. -/
noncomputable def reward {P : Instance} {K : ℕ} (q : Policy P K) (π : State P K → ℝ) : ℝ :=
  ∑ z, π z * ∑ i, ∑ j, P.Λ i j * q.1 z i j * P.I i j (q.1 z i j)

end VehShare.MultiNet


