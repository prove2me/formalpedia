-- Prove2me | Definitions.Def_FastCore_w
-- name    : FastCore_w
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:58.880872+00:00
-- url     : https://prove2.me/theorems/90b8c9e1-f18f-4104-9f0a-2efa292d37d6
-- title:
--   Maximum welfare $w(S)$ of a coalition
-- statement:
--   For a coalition $S\subseteq N$, the **maximum welfare** $w(S,\{b_i\})$ is the largest value of $\sum_{i\in N} b_i(x_i)$ over allocations $\{x_i\}_{i\in N}$ (pairwise disjoint bundles) that assign items only to agents in $S$, that is, with $x_i=\emptyset$ for $i\notin S$.
--
--   We write $w(S)$ when the bids are clear. This single function also gives the oracle's value $w(N,\{\max(b_i(.)-\pi_i,0)\})$, by applying it to the truncated bids.
--
--   **Formalization Note** The maximum is a `Finset.sup'` over the finite set of such allocations, which contains the all-empty allocation, so no junk value can occur. Allocations and welfare are the published `ComplementFreeCA.CFRounding.IsAllocation` and `ComplementFreeCA.CFRounding.welfare`.
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, §2, p.10

import Mathlib
import Definitions.Def_FastCore_Bids
import Definitions.Def_ComplementFreeCA_CFRounding_Auction

open ComplementFreeCA.CFRounding (IsAllocation welfare)

namespace FastCore

open scoped Classical in
/-- The maximum welfare `w(S, {bᵢ})` of the coalition `S`: the maximum of `∑ᵢ bᵢ(xᵢ)` over the
allocations that assign items only to agents in `S` (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, §2, p.10).

**Formalization Note.** The maximum is a `Finset.sup'` over the finite set of allocations `x` with
`xᵢ = ∅` for `i ∉ S`; the all-empty allocation shows that this set is nonempty, so no junk value
occurs. Allocations and welfare are the published
`ComplementFreeCA.CFRounding.IsAllocation` and `welfare`. `w` takes any `b`, so
`w (trunc b π) univ` is the paper's `w(N, {max(bᵢ(.) − πᵢ, 0)})`. -/
noncomputable def w {n m : ℕ} (b : Bids n m) (S : Finset (Fin n)) : ℝ :=
  (Finset.univ.filter (fun x : Fin n → Finset (Fin m) =>
      IsAllocation x ∧ ∀ i, i ∉ S → x i = ∅)).sup'
    ⟨fun _ => ∅, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fun _ _ _ => Finset.disjoint_empty_left _, fun _ _ => rfl⟩⟩ (welfare b)

end FastCore


