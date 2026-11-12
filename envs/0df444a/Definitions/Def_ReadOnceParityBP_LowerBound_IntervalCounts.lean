-- Prove2me | Definitions.Def_ReadOnceParityBP_LowerBound_IntervalCounts
-- name    : ReadOnceParityBP_LowerBound_IntervalCounts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:27:30.35423+00:00
-- url     : https://prove2.me/theorems/3e8fe78c-f5d1-45e5-911e-d05c8bf26944
-- title:
--   Independent local internal and external matching counts
-- statement:
--   Fix input bits x and y on n positions. For integer endpoints i,j, list the positions in [i,j] in increasing order. A local configuration C is a subset of this interval with twice its cardinality equal to the interval length. Run the canonical cyclic deletion process on that interval, and require every recorded pair to have distinct x-bits and every member of C to have y-bit one. I counts all such C; E counts those whose recorded pairs all point forward in ordinary order.
--
--   $$I_{i,j}=\#\{C:\operatorname{LocalValid}(C)\},\qquad E_{i,j}=\#\{C:\operatorname{LocalValid}(C),\ \forall(a,b)\in\sigma_C,\ a<b\}.$$
--
--   This is the declared reading of the ambiguous local-state prose on p.9. It counts local configurations independently of equations (2) and (3). Empty intervals have one empty configuration; odd intervals have none. Endpoints are integers, so [0,−1] is literally empty. The definitions clip arbitrary endpoints to the finite ambient positions; recurrence statements use intervals wholly inside that range. bitAt defaults to false outside the positions and bitNat turns a bit into the natural number zero or one. These states supply the semantic targets for the decomposition recurrences.
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), §3 local-state prose, base cases and equations (2)–(3), pp.9–10; local-state reading documented in MODERATION_NOTES.md; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_CanonicalMatching

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

/-- The elements of the integer interval `[i, j] ∩ {0, …, n-1}` of `ℤ_n`, in increasing
order (empty when `j < i`). -/
def intervalList (n : ℕ) (i j : ℤ) : List (Fin n) :=
  (List.finRange n).filter fun v => decide (i ≤ (v.val : ℤ) ∧ (v.val : ℤ) ≤ j)

/-- The local matchings of `[i, j]` used in §3 (pp. 9–10): a set `C` of exactly half of the
elements of `[i, j]`, matched by the canonical deletion process of Definition 2.3 run on the
cycle formed by the interval itself (`i, i+1, …, j`, then back to `i`), which is `x`-valid and
`y`-eligible: every matched pair `(a, b)` has `x_a ≠ x_b`, and `y_a = 1` for every `a ∈ C`. -/
def LocalValid {n : ℕ} (x y : Fin n → Bool) (i j : ℤ) (C : Finset (Fin n)) : Prop :=
  (∀ a ∈ C, i ≤ (a.val : ℤ) ∧ (a.val : ℤ) ≤ j) ∧ 2 * C.card = (intervalList n i j).length ∧
    (∀ q ∈ greedyPairs C n (intervalList n i j), x q.1 ≠ x q.2) ∧ ∀ a ∈ C, y a = true

/-- A local matching is external (linear) if all its directed pairs go from left to right in
the ordinary order of the interval, i.e. no pair wraps around the interval. -/
def Forward {n : ℕ} (i j : ℤ) (C : Finset (Fin n)) : Prop :=
  ∀ q ∈ greedyPairs C n (intervalList n i j), q.1 < q.2

open Classical in
/-- `Int_{i,j}` (§3, p. 9), in the local reading: the number of `x`-valid, `y`-eligible ways
to match the elements of `[i, j]` among themselves by a (cyclic) canonical matching. On the
full interval `[0, n-1]` it counts all `x`-valid, `y`-eligible sets `B`. For `j < i` (empty
interval) it equals `1`, and for odd length it equals `0`. -/
noncomputable def intCount {n : ℕ} (x y : Fin n → Bool) (i j : ℤ) : ℕ :=
  (((Finset.univ : Finset (Fin n)).powerset).filter fun C => LocalValid x y i j C).card

open Classical in
/-- `Ext_{i,j}` (§3, p. 9), in the local reading: the number of `x`-valid, `y`-eligible ways
to match the elements of `[i, j]` among themselves by a canonical matching all of whose
directed pairs go from left to right (no pair wraps around). For `j < i` it equals `1`, and for
odd length it equals `0`. -/
noncomputable def extCount {n : ℕ} (x y : Fin n → Bool) (i j : ℤ) : ℕ :=
  (((Finset.univ : Finset (Fin n)).powerset).filter
    fun C => LocalValid x y i j C ∧ Forward i j C).card

/-- The bit `x_i` at an integer index (`false` outside `{0, …, n-1}`). -/
def bitAt {n : ℕ} (x : Fin n → Bool) (i : ℤ) : Bool :=
  if h : 0 ≤ i ∧ i < (n : ℤ) then
    x ⟨i.toNat, by omega⟩ else false

/-- The bit `y_i`, as the natural number `0` or `1`. -/
def bitNat {n : ℕ} (y : Fin n → Bool) (i : ℤ) : ℕ :=
  if bitAt y i then 1 else 0

end ReadOnceParityBP.LowerBound


