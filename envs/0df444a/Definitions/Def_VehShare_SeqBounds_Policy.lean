-- Prove2me | Definitions.Def_VehShare_SeqBounds_Policy
-- name    : VehShare_SeqBounds_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:36:37.785063+00:00
-- url     : https://prove2.me/theorems/f5f35872-e3a1-46ab-9944-16f1853bd7f8
-- title:
--   Dynamic (state-dependent) pricing policies
-- statement:
--   A **dynamic pricing policy** assigns, in every state $x$ and for every pair $(i,j)$, the accepted fraction $q_{ij}(x)\in[0,1]$, with $q_{ij}(x)=0$ whenever location $i$ holds no vehicle (p. 5: "defining $q_{ij}(x)=0$ if the number of vehicles at location $i$ is $0$"). The effective demand rate is $\lambda_{ij}=q_{ij}(x)\Lambda_{ij}$.
--
--   No other restriction is imposed.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, §2, pp. 4–5

import Mathlib
import Definitions.Def_VehShare_SeqBounds_State

namespace VehShare.SeqBounds

/-- **Dynamic (state-dependent) pricing policies.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), §2, pp. 4–5 (unnumbered).

A policy gives, in every state `z` and for every pair `(i, j)`, the accepted fraction
`q z i j ∈ [0, 1]` (the quantile of the quoted price, p. 5), and `q z i j = 0` when location `i` holds
no vehicle (p. 5: "defining `q_ij(x) = 0` if the number of vehicles at location `i` is 0").
Nothing else is required. -/
abbrev Policy (P : Instance) (K : ℕ) : Type :=
  {q : State P K → P.L → P.L → ℝ //
    (∀ z i j, 0 ≤ q z i j ∧ q z i j ≤ 1) ∧ ∀ z i j, z.1 (Sum.inl i) = 0 → q z i j = 0}

end VehShare.SeqBounds


