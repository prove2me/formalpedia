-- Prove2me | Definitions.Def_KashUpgrade_sliceWeight
-- name    : KashUpgrade_sliceWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:21:05.700006+00:00
-- url     : https://prove2.me/theorems/f8e53230-2b18-4b95-969d-18e2fe078bdc
-- title:
--   The coefficients $A^j_j$ and $A^j_{j+i}$ of problem (12)
-- statement:
--   The coefficients of problem (12):
--   $$
--   A^j_j=\sum_{t'=s_j}^{s_{j+1}-1}\sum_{t=t'}^{t'+d-1}\delta^t,\qquad
--   A^j_{j+i}=\sum_{t'=s_j}^{s_{j+1}-1}\sum_{t=s_{j+i}}^{t'+d-1}\delta^t,\quad i\ge 1 .
--   $$
--   The sum over $t'$ runs over the arrival times of the slice and the sum over $t$ over the periods in which such a customer pays the price of the relevant class.
--
--   **Formalization Note** The arrival time runs over $t'\ge s_j$ when introduction $j+1$ does not exist (a convergent double sum). An empty inner sum is $0$, and $A^j_{j+i}=0$ if introduction $j+i$ does not exist. The index of the coefficient is the absolute class index.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), (37)–(38), p.49

import Mathlib
import Definitions.Def_KashUpgrade_IsIntroduced

namespace KashUpgrade

/-- **The coefficients of problem (12).** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), (37)–(38), p.49:
`A^j_j = ∑_{t'=s_j}^{s_{j+1}-1} ∑_{t=t'}^{t'+d-1} δ^t` and, for `i ≥ 1`,
`A^j_{j+i} = ∑_{t'=s_j}^{s_{j+1}-1} ∑_{t=s_{j+i}}^{t'+d-1} δ^t`, the second argument of this
function being the absolute index `j + i`.

**Formalization Note** The arrival time `t'` runs over the slice `s_j ≤ t' < s_{j+1}`, and for the
last introduction of a finite schedule over `t' ≥ s_j`, which gives a convergent double sum. An empty
inner sum is `0`, and `A^j_{j+i} = 0` when introduction `j + i` does not exist. -/
noncomputable def sliceWeight (S : Schedule) (d : ℕ) (δ : ℝ) (j i : ℕ) : ℝ :=
  open Classical in
  let inSlice : ℕ → Prop := fun t' => S.s j ≤ t' ∧ (IsIntroduced S (j + 1) → t' < S.s (j + 1))
  if i = j then
    ∑' t', if inSlice t' then ∑ t ∈ Finset.Icc t' (t' + d - 1), δ ^ t else 0
  else if IsIntroduced S i then
    ∑' t', if inSlice t' then ∑ t ∈ Finset.Icc (S.s i) (t' + d - 1), δ ^ t else 0
  else 0

end KashUpgrade


