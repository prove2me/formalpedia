-- Prove2me | Definitions.Def_MarketMakerAds_sortDesc
-- name    : MarketMakerAds_sortDesc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:01.302425+00:00
-- url     : https://prove2.me/theorems/869d774e-c7c0-46b7-8c0e-b3d5b27d6665
-- title:
--   Unit values sorted in decreasing order
-- statement:
--   For a finite list of unit values, $\mathrm{sortDesc}$ lists them as $v_1\ge v_2\ge\cdots$. Its entry at position $k$ (counting from $0$) is the $(k+1)$-th highest value, counting multiplicities. In particular the $(I+1)$-th highest value $v_{I+1}$, the auction clearing price, is the entry at position $I$.
--
--   **Formalization Note** Implemented by insertion sort for the order $\ge$; the sorted rearrangement of a list is unique, so the choice of algorithm does not matter.
-- source:
--   Cohen, Désir, Korula, Sivan, Best of Both Worlds Ad Contracts, SSRN 3088600, §3.1, p.10 ($v_{I+1}$, the $(I+1)$-th highest value including multiplicities); Assumption 2, p.11

import Mathlib

namespace MarketMakerAds

/-- **A list of unit values sorted in decreasing order.**
Cohen, Désir, Korula, Sivan, *Best of Both Worlds Ad Contracts*, SSRN 3088600, §3.1, p.10
("v_{I+1}, which is the (I + 1)-th highest value (including the non-unit demand
multiplicities)") and Assumption 2, p.11 ("the allocated buyer-item pairs are still the ones with
values v_1, …, v_I").

`sortDesc l` is `l` sorted so that `v_1 ≥ v_2 ≥ …`; its entry at index `k` (from `0`) is the
`(k+1)`-th highest value.

**Formalization Note** Insertion sort for the order `≥`; any sorting algorithm gives the same
list, since the sorted permutation of a list is unique. -/
noncomputable def sortDesc (l : List ℝ) : List ℝ :=
  l.insertionSort (fun a b => b ≤ a)

end MarketMakerAds


