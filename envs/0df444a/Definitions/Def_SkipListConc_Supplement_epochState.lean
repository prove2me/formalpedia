-- Prove2me | Definitions.Def_SkipListConc_Supplement_epochState
-- name    : SkipListConc_Supplement_epochState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:50:08.110545+00:00
-- url     : https://prove2.me/theorems/609b79b7-1742-4f20-87ee-c9e4a34b42f7
-- title:
--   Epoch schedule of epochal reseeding (Definition 1.6)
-- statement:
--   Let $d_t$ be the number of distinct items inserted by time $t$ and the **capacity** the least power of two $N\ge d_t$. The operations are divided into **epochs**: an epoch begun at capacity $N$ ends after $N$ charges, or earlier, immediately before an insertion that would raise the capacity; the insertion that ends an epoch belongs to the next one, which begins at the raised capacity. The first operation opens the first epoch at capacity $1$.
--
--   For each operation $t$, $\mathrm{epochState}(\sigma,t)=(r,N,c)$ records the epoch $r$ it belongs to, the capacity $N$ at which that epoch began, and its rank $c\ge1$ among the epoch's charges. The schedule depends only on $\sigma$.
--
--   **Formalization Note** Epochs and positions are 0-based; the capacity is $2^{\lceil\log_2 d\rceil}$ (`2 ^ Nat.clog 2 d`), which is $1$ for $d\le1$. Checked on a nine-operation example in the verification file.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Definition 1.6, p.10

import Mathlib

namespace SkipListConc.Supplement

/-- The epoch schedule of epochal reseeding, Definition 1.6 (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), Definition 1.6, p.10).
`epochState σ t = (r, N, c)`: operation `t` (0-based) belongs to epoch `r` (0-based), begun at
capacity `N`, and is the `c`-th charge of that epoch (`c ≥ 1`).

With `d_t` the number of distinct items inserted by time `t` and the capacity the least power of
two `≥ d_t` (`2 ^ Nat.clog 2 d_t`, which is `1` for `d_t ≤ 1`): an epoch begun at capacity `N`
ends after `N` charges, or earlier, immediately before an insertion that would raise the
capacity; the insertion that ends an epoch belongs to the next one, whose capacity is the raised
one. The first operation opens epoch `0` at capacity `1`.

**Formalization Note** The schedule is a deterministic function of `σ` only. Operation `t + 1`
opens a new epoch iff the capacity computed with the items of `σ.take (t + 2)` exceeds the
current epoch's capacity (which happens only at an insertion) or the current epoch already has
`N` charges; the new epoch's capacity is the current least power of two `≥ d_{t+1}`. -/
def epochState {α : Type*} [DecidableEq α] (σ : List α) : ℕ → ℕ × ℕ × ℕ
  | 0 => (0, 1, 1)
  | t + 1 =>
      let s := epochState σ t
      let N' := 2 ^ Nat.clog 2 (σ.take (t + 2)).toFinset.card
      if s.2.1 < N' ∨ s.2.2 = s.2.1 then (s.1 + 1, N', 1) else (s.1, s.2.1, s.2.2 + 1)

end SkipListConc.Supplement


