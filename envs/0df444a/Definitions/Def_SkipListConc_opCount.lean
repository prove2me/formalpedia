-- Prove2me | Definitions.Def_SkipListConc_opCount
-- name    : SkipListConc_opCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:00.756248+00:00
-- url     : https://prove2.me/theorems/64cee4b5-c89a-4afa-b65d-30aa84b2d8a9
-- title:
--   Number of operations on an item before time $t$
-- statement:
--   An **operation sequence** is a finite list $\sigma=(x_1,\dots,x_F)$ of items, fixed in advance; the first occurrence of an item is its insertion and later occurrences are accesses. For an item $y$ and a position $t$, $\mathrm{opCount}(\sigma,y,t)$ is the number of operations on $y$ strictly before position $t$.
--
--   For the target $x_t$ of operation $t$ this is $f_t-1$; for another item $y$ it is $f_y(t)$, the number of its operations so far.
--
--   **Formalization Note** Positions are 0-based: position $t$ is the paper's operation $t+1$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §1.1, p.5

import Mathlib

namespace SkipListConc

/-- The number of operations on item `y` strictly before position `t` of the operation sequence
`σ` (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), §1.1, p.5).

**Formalization Note** The sequence is a list `σ` of items, 0-based: position `t` is the paper's
operation `t + 1`. The first occurrence of an item is its insertion, later ones are accesses.
For the target `x_t = σ[t]`, `opCount σ x_t t = f_t − 1`; for another item `y` it is `f_y(t)`. -/
def opCount {α : Type*} [DecidableEq α] (σ : List α) (y : α) (t : ℕ) : ℕ :=
  (σ.take t).count y

end SkipListConc


