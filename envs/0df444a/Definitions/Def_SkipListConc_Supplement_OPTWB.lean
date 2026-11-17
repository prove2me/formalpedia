-- Prove2me | Definitions.Def_SkipListConc_Supplement_OPTWB
-- name    : SkipListConc_Supplement_OPTWB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:56:53.955776+00:00
-- url     : https://prove2.me/theorems/563f6e06-cb60-4056-9b4e-658f5caee4bb
-- title:
--   Weakly $B$-bounded offline optimum $\mathrm{OPT}_{WB}(X)$
-- statement:
--   Let $S$ be the item set and $X=(X_1,\dots,X_m)$ an access sequence. An **offline server** is a sequence of height functions $h_0,h_1,\dots,h_m$ on $S$ (heights $\ge1$), each weakly $B$-bounded; $h_0$ is chosen freely at no cost. Access $i$ searches for $X_i$ in the configuration $h_{i-1}$, paying $\mathrm{cost}-1$ finger moves (each step forward, up or down from the top of the header costs one), and then passes to $h_i$, which may differ from $h_{i-1}$ only at items that search touched, paying one unit per level by which each height changes. Then
--   $$
--   \mathrm{OPT}_{WB}(X)=\min_{\text{offline servers}}\ \sum_{i=1}^{m}\Bigl(\mathrm{cost}_{h_{i-1}}(X_i)-1+\sum_{y\in S}|h_i(y)-h_{i-1}(y)|\Bigr).
--   $$
--   Insertions are not accesses and are not paid.
--
--   **Formalization Note** The minimum is the infimum of a set of natural numbers; the set is nonempty (a configuration with distinct heights is weakly $B$-bounded and can be kept fixed), so the minimum is attained — proved in the verification file.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Theorem F, p.11; §5.3, p.35, after [BDL08]

import Mathlib
import Definitions.Def_SkipListConc_searchCost
import Definitions.Def_SkipListConc_Supplement_IsWeaklyBounded
import Definitions.Def_SkipListConc_Supplement_touched

namespace SkipListConc.Supplement

/-- The weakly `B`-bounded offline optimum `OPT_WB(X)` (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), Theorem F, p.11, and §5.3,
p.35, after [BDL08]) of an access sequence `X = xs` on the item set `S`: the least cost at which a
skip list that knows `X` in advance and is weakly `B`-bounded at all times serves `X`.

An offline server is a sequence of height functions `h 0, h 1, …, h m` (`m = |X|`), heights
`≥ 1` on `S`, each weakly `B`-bounded; `h 0` is chosen freely at no cost. Access `i` (0-based)
searches for `X_i` in the configuration `h i`, paying `searchCost S (h i) X_i − 1` finger moves
(each step forward, up or down costs one, from the top of the header), and then passes to
`h (i + 1)`, which may differ from `h i` only at items that search touched, paying one unit per
level by which each height changes.

**Formalization Note** `OPT_WB` is the infimum of a set of natural numbers, attained when the set
is nonempty; it is nonempty because any configuration with distinct heights is weakly
`B`-bounded and can be kept unchanged. Insertions are not accesses of `X` and are not paid. -/
noncomputable def OPTWB {α : Type*} [LinearOrder α] (B : ℕ) (S : Finset α) (xs : List α) : ℕ :=
  sInf {c : ℕ | ∃ h : ℕ → α → ℕ,
    (∀ i, i ≤ xs.length → (∀ y ∈ S, 1 ≤ h i y) ∧ IsWeaklyBounded B S (h i)) ∧
    (∀ i : Fin xs.length, ∀ y ∈ S, h (i + 1) y ≠ h i y → y ∈ touched S (h i) (xs.get i)) ∧
    c = ∑ i : Fin xs.length,
      ((searchCost S (h i) (xs.get i) - 1) +
        ∑ y ∈ S, Int.natAbs ((h (i + 1) y : ℤ) - h i y))}

end SkipListConc.Supplement


