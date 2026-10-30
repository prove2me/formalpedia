-- Prove2me | Definitions.Def_VehShare_MultiNet_staticPolicy
-- name    : VehShare_MultiNet_staticPolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:44:16.621885+00:00
-- url     : https://prove2.me/theorems/c37edb08-75ed-4768-ad84-3ca2e6d6705b
-- title:
--   The static pricing policy induced by $q^s$
-- statement:
--   Given $q^s\in[0,1]^{\mathcal N\times\mathcal N}$, the **static policy** uses the fixed fractions $q^s$ whenever a vehicle is available:
--
--   $$
--   q_{ij}(x)=\begin{cases}q^s_{ij}, & x_i\ge1,\\ 0,& x_i=0.\end{cases}
--   $$
--
--   It is a dynamic policy in the sense of the model (prices that do not depend on the state, p. 6, with p. 5's convention at empty locations).
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, §3, p. 6

import Mathlib
import Definitions.Def_VehShare_MultiNet_Policy

namespace VehShare.MultiNet

/-- **The static pricing policy induced by `q^s`.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), §3, p. 6 (unnumbered): a static policy has "fixed prices that do not depend on the state of
system"; with p. 5's convention, the accepted fraction is `q^s_ij` when location `i` holds a vehicle
and 0 otherwise.

The argument `hqs` (`0 ≤ q^s ≤ 1`, part of feasibility for Problem (2)) makes it a `Policy`. -/
def staticPolicy (P : Instance) (K : ℕ) (qs : P.L → P.L → ℝ)
    (hqs : ∀ i j, 0 ≤ qs i j ∧ qs i j ≤ 1) : Policy P K :=
  ⟨fun z i j => if 1 ≤ z.1 (Sum.inl i) then qs i j else 0, by
    refine ⟨fun z i j => ?_, fun z i j hz => ?_⟩
    · show 0 ≤ (if 1 ≤ z.1 (Sum.inl i) then qs i j else 0) ∧
        (if 1 ≤ z.1 (Sum.inl i) then qs i j else 0) ≤ 1
      split_ifs
      · exact hqs i j
      · exact ⟨le_refl 0, zero_le_one⟩
    · simp [hz]⟩

end VehShare.MultiNet


