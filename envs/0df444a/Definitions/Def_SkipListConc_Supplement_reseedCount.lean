-- Prove2me | Definitions.Def_SkipListConc_Supplement_reseedCount
-- name    : SkipListConc_Supplement_reseedCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:50:37.837847+00:00
-- url     : https://prove2.me/theorems/d17fab43-534a-449e-8109-09f9621aa365
-- title:
--   Number of height draws of an item in the current epoch
-- statement:
--   Under epochal reseeding, at the start of each epoch the height of every item present is re-initialized as at insertion. For an operation $t$ and an item $y$, $\mathrm{reseedCount}(\sigma,t,y)$ is the number of height draws $y$ has had in the epoch of $t$ before $t$: one at the epoch start if $y$ was present then, plus one per operation on $y$ in the epoch strictly before $t$ (an insertion during the epoch is the item's first draw).
--
--   **Formalization Note** The epoch of $t$ starts at position $t+1-c$, with $c$ the rank of $t$ in its epoch.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Definition 1.6, p.10

import Mathlib
import Definitions.Def_SkipListConc_Supplement_epochState

namespace SkipListConc.Supplement

/-- The number of height draws item `y` has had in the current epoch before operation `t`
under epochal reseeding (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), Definition 1.6, p.10): one draw at the epoch's start if `y`
was present then (the re-initialization "as done at insertion"), plus one per operation on `y` in
the epoch strictly before `t` (its insertion, if inserted in the epoch, is its first draw).

**Formalization Note** The epoch of `t` starts at position `s = t + 1 − c`, `c` the third
component of `epochState σ t`; the items present at its start are those of `σ.take s`. -/
def reseedCount {α : Type*} [DecidableEq α] (σ : List α) (t : ℕ) (y : α) : ℕ :=
  let s := t + 1 - (epochState σ t).2.2
  (if y ∈ σ.take s then 1 else 0) + ((σ.drop s).take (t - s)).count y

end SkipListConc.Supplement


