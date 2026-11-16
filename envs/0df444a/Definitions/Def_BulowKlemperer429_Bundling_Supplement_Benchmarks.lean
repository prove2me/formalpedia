-- Prove2me | Definitions.Def_BulowKlemperer429_Bundling_Supplement_Benchmarks
-- name    : BulowKlemperer429_Bundling_Supplement_Benchmarks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:37:11.337443+00:00
-- url     : https://prove2.me/theorems/fab06393-1911-4da1-8698-8e55dc00532f
-- title:
--   Separate optimal auctions $\mathrm{SREV}_k$ and posted prices for bundles
-- statement:
--   For independent item laws $F_j$ and $k$ bidders, $\mathrm{SREV}_k(D)=\sum_j\mathrm{REV}_k(F_j)$ is the revenue of selling every item through its optimal single-item auction to $k$ independent bidders, where $\mathrm{REV}_k$ is the published optimal scalar-auction revenue. For bundles $B_1,\dots,B_n$ of items and prices $p_1,\dots,p_n\ge0$, the posted-price revenue from one additive bidder is
--   $$\sum_{i=1}^np_i\Pr\Big[\sum_{j\in B_i}V_j\ge p_i\Big].$$
--
--   For pairwise-disjoint bundles the bidder's purchase decisions separate, so this is the revenue of the menu that offers each bundle at its own price, the object of the lower bounds in Section 5.
--
--   **Formalization Note** Revenues are extended nonnegative reals. The definition does not require disjointness or nonemptiness; the theorems impose them.
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 7, §2, SREV_k; §1.1 p. 2 and §5 pp. 17, 19 posted prices for disjoint bundles (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
import Definitions.Def_BulowKlemperer429_Bundling_ScalarAuction
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling.Supplement

/-- Section 2, p. 7: `SREV_k(D) = Σ_j REV_k(F_j)`, each item sold through its optimal single-item
auction to `k` independent bidders (the published `REVk`). -/
noncomputable def SREVk {ι : Type} [Fintype ι] (k : ℕ) (ν : ι → Measure ℝ≥0) : ℝ≥0∞ :=
  ∑ j, REVk k (ν j)

/-- Sections 1.1 and 5, pp. 2, 17, 19: revenue of posted prices `p i` for bundles `B i` sold to
one additive bidder with independent item values `V_j ∼ ν j`:
`Σ_i p_i · Pr[Σ_{j ∈ B_i} V_j ≥ p_i]`. For pairwise-disjoint bundles the purchase decisions
separate, so this is the revenue of the posted-price menu; the weak inequality is the paper's
posted-price convention (p. 6). Disjointness is imposed by the theorems, not here. -/
noncomputable def bundlePriceRevenue {ι : Type} [Fintype ι] {n : ℕ} (ν : ι → Measure ℝ≥0)
    (B : Fin n → Finset ι) (p : Fin n → ℝ≥0) : ℝ≥0∞ :=
  ∑ i, (p i : ℝ≥0∞) * Measure.pi ν {v | p i ≤ ∑ j ∈ B i, v j}

end BulowKlemperer429.Bundling.Supplement


