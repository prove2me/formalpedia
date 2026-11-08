-- Prove2me | Definitions.Def_TightClock_treeWeight
-- name    : TightClock_treeWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:09:07.505208+00:00
-- url     : https://prove2.me/theorems/a5306434-2002-4ba3-a259-056d005459cd
-- title:
--   Probability of a realized tree
-- statement:
--   All coins of the tree are independent and each is true with probability $a$. So a realization $T$ has probability
--
--   $$\prod_{D}\prod_{i}\big(a\,\mathbb 1[T_D(i)]+(1-a)\,\mathbb 1[\neg T_D(i)]\big).$$
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Instance 11, §6.2, p.35 (PDF p.38)

import Mathlib
import Definitions.Def_TightClock_a
import Definitions.Def_TightClock_Tree

set_option autoImplicit false

namespace TightClock

/-- The probability of a realized tree: all coins are independent Bernoulli(`a`). Afshinmehr et al.,
manuscript (STOC 2027 submission), Instance 11, §6.2, p.35 (PDF 38). -/
noncomputable def treeWeight (q L : ℕ) (T : Tree q L) : ℝ :=
  ∏ D : NonrootNode q L, ∏ i : Fin (bidderCount q L), if T D i then a q else 1 - a q

end TightClock


