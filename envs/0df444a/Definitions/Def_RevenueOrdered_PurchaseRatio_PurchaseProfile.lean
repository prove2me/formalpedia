-- Prove2me | Definitions.Def_RevenueOrdered_PurchaseRatio_PurchaseProfile
-- name    : RevenueOrdered_PurchaseRatio_PurchaseProfile
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:50:15.549201+00:00
-- url     : https://prove2.me/theorems/e053ffef-ed6d-4f90-ab43-504c6fbf4752
-- title:
--   Theorem 3.3, p. 9 — purchase profile N_i of an assortment S∗ and the sum ∑ (N_i − N_{i+1})/N_i
-- statement:
--   Let $S^*\subseteq\mathcal C$ be an assortment. For $i\in[k]$ its **purchase profile** is
--   $$
--   N_i=\sum_{\substack{x\in S^*\\ r(x)\ge r_i}}\mathcal P(x,S^*),
--   $$
--   the probability that a consumer offered $S^*$ buys a product of revenue at least $r_i$. Following the paper, $N_{k+1}:=0$. For an index $\ell$ the mission uses the sum
--   $$
--   \sum_{i=1}^{\ell}\frac{N_i-N_{i+1}}{N_i}.
--   $$
--   In Theorem 3.3, $S^*$ is optimal and $\ell$ is the largest index with $N_\ell>0$; the reciprocal of this sum is then an approximation factor of revenue-ordered assortments.
--
--   **Formalization Note** `purchaseProfile P r S i` is $N_i$ for $1\le i\le k$ and $0$ for every other index; in particular $N_{k+1}=0$, the paper's convention. `purchaseRatioSum P r S ℓ` is the displayed sum. Both are defined for any $S^*$; optimality is a hypothesis of the theorem that needs it.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 9, Theorem 3.3 and its proof (N_{k+1} := 0)

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_RevenueOrdered_Ratio_RevenueOrdered

namespace RevenueOrdered.PurchaseRatio

noncomputable section

variable {C : Type*} [Fintype C]

/-- The purchase profile of a set `S∗` (Theorem 3.3, p. 9), 1-based:
for `1 ≤ i ≤ k`, `purchaseProfile P r S i = N_i = ∑_{x ∈ S∗, r(x) ≥ r_i} 𝒫(x, S∗)`, the
probability that a consumer offered `S∗` buys a product of revenue at least `r_i`.
For every other index the value is `0`; in particular `N_{k+1} = 0`, which is the paper's
convention "`N_{k+1} := 0`" in the proof of Theorem 3.3. -/
def purchaseProfile (P : C → Finset C → ℝ) (r : C → ℝ) (S : Finset C) (i : ℕ) : ℝ :=
  if 1 ≤ i ∧ i ≤ RevenueOrdered.Ratio.numVals r then ∑ x ∈ S.filter (fun x => RevenueOrdered.Ratio.level r i ≤ r x), P x S else 0

/-- The quantity `∑_{i=1}^{ℓ} (N_i − N_{i+1}) / N_i` of Theorem 3.3 (p. 9), for the purchase
profile `N` of `S∗` and an index `ℓ`. -/
def purchaseRatioSum (P : C → Finset C → ℝ) (r : C → ℝ) (S : Finset C) (ℓ : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 ℓ,
    (purchaseProfile P r S i - purchaseProfile P r S (i + 1)) / purchaseProfile P r S i

end

end RevenueOrdered.PurchaseRatio


