-- Prove2me | Definitions.Def_AKSZigZag_halvingNearsort
-- name    : AKSZigZag_halvingNearsort
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:12.418203+00:00
-- url     : https://prove2.me/theorems/3e556699-461b-4fea-a57d-f94ced76712e
-- title:
--   The recursive-halving $\varepsilon$-nearsort network of §4
-- statement:
--   Let $h_k$ be a comparator network on $k$ registers for every $k$; in the paper $h_k$ is an $\varepsilon_1$-halver. The **recursive-halving network** on $m$ registers is built as follows:
--   1. apply $h_m$ to all $m$ registers;
--   2. apply the halvers, simultaneously, to the lower half (the first $\lfloor m/2\rfloor$ registers) and to the upper half;
--   3. continue with quarters, eighths, and so on.
--
--   A piece is halved exactly when it has at least two registers and its size is at least $\varepsilon m$. So the recursion stops when the pieces have size $w<\varepsilon m$.
--
--   This is the paper's construction of an $\varepsilon$-nearsort from $\varepsilon_1$-halvers, with $\varepsilon_1<\varepsilon/\log(1/\varepsilon)$. Since the number of levels depends only on $\varepsilon$, its depth is bounded independently of $m$.
--
--   **Formalization Note** A piece of odd size is split with the smaller half below. A piece of size $1$ is never split, which also makes the recursion terminate when $\varepsilon m\le1$.
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §4, p.5 ("To construct an ε-nearsort network …")

import Mathlib
import Definitions.Def_AKSSorting_Core_ComparatorNetwork
import Definitions.Def_AKSZigZag_NetworkOps

namespace AKSZigZag

open AKSSorting.Core

/-- The block of registers `lo, lo+1, …, lo+len-1` of `Fin m` (0-based). -/
def block (m lo len : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun r : Fin m => lo ≤ r.val ∧ r.val < lo + len

/-- The layers of the recursive halving schedule of AKS, STOC 1983, §4, p.5, on the piece of
`len` registers starting at `lo`: if the piece has at least two registers and size `len ≥ εm`,
run the halver `h len` on it, then recurse, simultaneously, on its lower half (the first
`⌊len/2⌋` registers) and its upper half (the other `len - ⌊len/2⌋`); otherwise do nothing. -/
noncomputable def halvingLayers {m : ℕ} (h : (k : ℕ) → ComparatorNetwork k) (ε : ℝ) :
    ℕ → ℕ → List (List (Fin m × Fin m))
  | lo, len =>
    if 2 ≤ len ∧ ε * m ≤ len then
      parallelLayers h [block m lo len] ++
        mergeLayers (halvingLayers h ε lo (len / 2))
          (halvingLayers h ε (lo + len / 2) (len - len / 2))
    else []
termination_by _ len => len
decreasing_by all_goals omega

/-- **The ε-nearsort network built from ε₁-halvers** (AKS, STOC 1983, §4, p.5): "apply an
ε1-halver (network) … to the whole set of registers, then apply ε1-halvers to the top and bottom
half of registers, then to each quarter, eighth, sixteenth, until the pieces have size w < εm."
Here `h k` is the halver used on a piece of `k` registers.

**Formalization Note.** A piece is halved exactly when its size is at least `εm` (and at least
2: a single register is never split). Pieces of odd size are split with the lower half of size
`⌊len/2⌋`, as in §3's `A = (1, …, ⌊m/2⌋)`. Halvers on the pieces of one level run
simultaneously (their layers are merged), and the levels run one after another. -/
noncomputable def halvingNearsort (h : (k : ℕ) → ComparatorNetwork k) (ε : ℝ) (m : ℕ) :
    ComparatorNetwork m :=
  mkNet (halvingLayers (m := m) h ε 0 m)

end AKSZigZag


