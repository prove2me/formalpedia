-- Prove2me | Definitions.Def_KashUpgrade_IsUpgradeBoundAt
-- name    : KashUpgrade_IsUpgradeBoundAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:21:17.72048+00:00
-- url     : https://prove2.me/theorems/33b8968b-cd51-4d87-904b-8ea9637ab583
-- title:
--   $n$ bounds the upgrade experience in slice $j$
-- statement:
--   A customer of slice $j$ is in the system until time $s_{j+1}+d-2$ at the latest, so she can reach class $j+i$ only if $s_{j+i}\le s_{j+1}+d-2$. The number $n$ bounds the upgrade experience of slice $j$ if every $i\ge 1$ such that class $j+i$ exists and $s_{j+i}\le s_{j+1}+d-2$ satisfies $i\le n$.
--
--   The paper takes $n$ to be the maximum possible customer upgrade experience, with $n\le d-1$.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), pp.9–10

import Mathlib
import Definitions.Def_KashUpgrade_IsIntroduced

namespace KashUpgrade

/-- **`n` bounds the upgrade experience of slice `j`.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), pp.9–10: "We take `n` to be the maximum
possible customer upgrade experience". A customer of slice `j` is in the system until
`s_{j+1} + d - 2` at the latest, so she can reach class `j + i` only if
`s_{j+i} ≤ s_{j+1} + d - 2`. This predicate says that every such `i` is at most `n`. -/
def IsUpgradeBoundAt (S : Schedule) (d j n : ℕ) : Prop :=
  ∀ i, 1 ≤ i → IsIntroduced S (j + i) → S.s (j + i) ≤ S.s (j + 1) + d - 2 → i ≤ n

end KashUpgrade


