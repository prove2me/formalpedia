-- Prove2me | Definitions.Def_TightClock_Supplement_routedDisjoint
-- name    : TightClock_Supplement_routedDisjoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:20:42.54917+00:00
-- url     : https://prove2.me/theorems/a7bd4e53-92c5-460d-8c33-00c0c9fb3284
-- title:
--   Auction 9 — $\mathrm{RoutedDisjoint}$
-- statement:
--   **Auction 9 (RoutedDisjoint).** Draw a uniformly random ordering $\sigma$ of the maximal sets $G_1,\dots,G_k$ of $\mathcal F$. Each bidder $i$ goes to $L_i$, the first maximal set in $\sigma$ that contains her, and $A_j=\{i:L_i=j\}=G_j\setminus\bigcup_{\ell\text{ before }j}G_\ell$. Run Auction 4 on the nonempty $A_j$ with fresh randomness. No offers are made before Auction 4 starts.
--
--   **Formalization Note** The ordering is realized by independent uniform keys, one per set of bidders (the order of increasing keys); ties have probability $0$ and are broken by the selection rule.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §5.1.4, Auction 9, p.30 (PDF p.33)

import Mathlib
import Definitions.Def_TightClock_Supplement_disjointProg
import Definitions.Def_BayesClock_maximalSets

set_option autoImplicit false

namespace TightClock.Supplement

/-- Auction 9, `RoutedDisjoint`, for a downward-closed `F` with maximal sets `G₁, …, G_k`. Draw a
uniformly random ordering `σ` of the maximal sets, realized by i.i.d. uniform keys `κ_G` (the order of
increasing keys, ties broken by `sel`). Each bidder `i` goes to `Lᵢ`, the first maximal set in `σ`
containing her, and `A_j = {i : Lᵢ = G_j}`. Run Auction 4 on the nonempty `A_j`, with fresh
randomness `ω`. No offers are made before Auction 4 starts. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §5.1.4, Auction 9, p.30
(PDF 33).

**Formalization Note** Ordering by i.i.d. continuous keys is a uniformly random ordering; ties have
probability `0`. -/
noncomputable def routedDisjoint {n : ℕ} (δ : ℝ) (F : Finset (Finset (Fin n))) (sel : Selector n)
    (key : Finset (Fin n) → unitInterval) (ω : DisjointSeed n) : ClockProg n (Finset (Fin n)) :=
  let label : Fin n → Finset (Fin n) := fun i =>
    sel.pick ((BayesClock.maximalSets F).filter (fun G => i ∈ G)) (fun G => - (key G : ℝ))
  let A : Finset (Fin n) → Finset (Fin n) := fun G => Finset.univ.filter (fun i => label i = G)
  disjointProg δ (((BayesClock.maximalSets F).image A).filter (fun S => S.Nonempty)) sel ω

end TightClock.Supplement


