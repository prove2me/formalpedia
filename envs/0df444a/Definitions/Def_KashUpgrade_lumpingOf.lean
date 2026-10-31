-- Prove2me | Definitions.Def_KashUpgrade_lumpingOf
-- name    : KashUpgrade_lumpingOf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:31.186131+00:00
-- url     : https://prove2.me/theorems/0bea7afa-a1b0-4f1f-9c63-8484b9f2ebfa
-- title:
--   The lumping of a threshold vector
-- statement:
--   A lumping is a subset of the equality constraints $\{\theta^j_i=\theta^j_{i+1}\mid j+1\le i<j+n\}$, recorded here as the set of those indices $i$. The lumping of a threshold vector is the set of constraints that it satisfies.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), §4.2.2, p.16; §4.3.1, p.17

import Mathlib

namespace KashUpgrade

/-- **The lumping of a threshold vector.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), §4.2.2, p.16 and §4.3.1, p.17: a lumping is a subset
of the constraints `{θ_i = θ_{i+1} | j + 1 ≤ i < j + n}`, recorded as the set of those `i`, and
the lumping of `θ` is the set of constraints that `θ` satisfies. -/
noncomputable def lumpingOf (j n : ℕ) (θ : ℕ → ℝ) : Finset ℕ :=
  open Classical in
  (Finset.Ico (j + 1) (j + n)).filter fun i => θ i = θ (i + 1)

end KashUpgrade


