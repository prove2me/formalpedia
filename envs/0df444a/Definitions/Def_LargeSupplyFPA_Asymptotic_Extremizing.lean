-- Prove2me | Definitions.Def_LargeSupplyFPA_Asymptotic_Extremizing
-- name    : LargeSupplyFPA_Asymptotic_Extremizing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:02:45.054215+00:00
-- url     : https://prove2.me/theorems/8c09703e-bb62-4584-9d0d-15311f6b4280
-- title:
--   Extremizing sequence of bid pairs along a subsequence (Definition, p. 10)
-- statement:
--   A sequence of **bid pairs** assigns to every auction $A^{(k)}$ bids $0\le\underline b^{(k)}\le\overline b^{(k)}$. It is **extremizing along the subsequence** $(A^{(k_l)})_{l\ge1}$ ($k_1<k_2<\cdots$) if
--   $$\lim_{l\to\infty}B^{(k_l)}\big(\underline b^{(k_l)}\big)=0\qquad\text{and}\qquad\lim_{l\to\infty}B^{(k_l)}\big(\overline b^{(k_l)}\big)=1,$$
--   where $B^{(k)}$ is the distribution function of the $k$-th highest bid in $A^{(k)}$. "Extremizing over the sequence" means along the whole sequence ($k_l=l$).
--
--   **Formalization Note** A subsequence is a strictly increasing $\varphi:\mathbb N\to\mathbb N$, and the auction $A^{(\varphi(l))}$ keeps its own unit count $\varphi(l)$. Both limits are `Tendsto` statements, so they are required to exist.
-- source:
--   Hartline, Shah, vonAllmen, Robust Analysis of First-Price Auctions with Large Supply, STOC 2027 submission (manuscript of November 3, 2026, sha256 2ad8363b…), p. 10, Definition (Extremizing Sequence Of Bid Pairs)

import Mathlib
import Definitions.Def_LargeSupplyFPA_Asymptotic_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace LargeSupplyFPA.Asymptotic

/-- A sequence of bid pairs `0 ≤ lo k ≤ hi k` (one pair for every auction `A^(k)`) is
extremizing along the subsequence of auctions `A^(φ l)` (`φ` strictly increasing) if
`B^(φ l)(lo (φ l)) → 0` and `B^(φ l)(hi (φ l)) → 1` as `l → ∞`, where `B^(k)` is the
distribution function of the `k`-th highest bid in the `k`-th auction. -/
def IsExtremizing (n : ℕ → ℕ) (V : ∀ k, Fin (n k) → Measure ℝ)
    (E : ∀ k, Fin (n k) → Kernel ℝ ℝ) (lo hi : ℕ → ℝ) (φ : ℕ → ℕ) : Prop :=
  StrictMono φ ∧ (∀ k, 0 ≤ lo k ∧ lo k ≤ hi k) ∧
    Tendsto (fun l => kthBidCDF (φ l) (V (φ l)) (E (φ l)) (lo (φ l))) atTop (𝓝 0) ∧
    Tendsto (fun l => kthBidCDF (φ l) (V (φ l)) (E (φ l)) (hi (φ l))) atTop (𝓝 1)

end LargeSupplyFPA.Asymptotic


