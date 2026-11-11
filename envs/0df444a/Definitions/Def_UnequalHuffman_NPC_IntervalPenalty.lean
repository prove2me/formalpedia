-- Prove2me | Definitions.Def_UnequalHuffman_NPC_IntervalPenalty
-- name    : UnequalHuffman_NPC_IntervalPenalty
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:44:21.419192+00:00
-- url     : https://prove2.me/theorems/14a1c28e-af3a-4b0c-814f-0f1889ff49db
-- title:
--   Interval constraints of Lemma A.1: interval systems, the coefficients g, the constants S* and Q₀, the score Q and the quadratic penalty
-- statement:
--   Interval data (Appendix A.1) assign to every sorted leaf position $(t,k)$, $1 \le t \le H$, $1 \le k \le n_t$, an integer interval $[\ell_{t,k}, r_{t,k}]$ (`IntervalData = List (List (ℤ × ℤ))`, row $t$ at index $t-1$; the leaf profile is $n_t$ = the row length and $H$ the number of rows). `IsIntervalSystem`: every interval has width at most one, $\ell \le r \le \ell + 1$, and at each depth both endpoint lists are nondecreasing. A tree **respects** the intervals (`Respects`) if $\ell_{t,k} \le z_{t,k}(T) \le r_{t,k}$ for all positions.
--
--   The explicit quantities of the proof of Lemma A.1 are
--   $$g_{t,k} = -2^{H-t}(\ell_{t,k} + r_{t,k} + H - t),\qquad S^* = \sum_{t=0}^{H-1} I_t\, 2^{H-t-1}(H-t),\qquad Q_0 = -S^* - \sum_{t,k} 2^{H-t}\ell_{t,k} r_{t,k},$$
--   with $I_t$ the internal counts of the profile, the linear score $Q(T) = \sum_{t,k} g_{t,k}\, z_{t,k}(T)$, and the penalty $\sum_{t,k} 2^{H-t}(z_{t,k}-\ell_{t,k})(z_{t,k}-r_{t,k})$.
--
--   Example (p. 40): singleton intervals $[0,0]$, $[1,1]$, $[2,2]$ give $S^* = 5$, $g = (-2), (-2,-4)$ and $Q_0 = -10$.
-- source:
--   Chandran and Gajjala, Binary Huffman Coding with Unequal Letter Costs Is NP-Complete, arXiv:2611.04444v1, p. 39, Appendix A.1 (intervals, Lemma A.1 and its proof)

import Mathlib
import Definitions.Def_UnequalHuffman_NPC_Trees

set_option autoImplicit false

namespace UnequalHuffman.NPC

/-- Interval data for Lemma A.1 (Appendix A.1): row `t - 1` (0-based) lists, for the sorted
leaf positions `k = 1, …, n_t` at depth `t`, the permitted integer interval `[ℓ_{t,k}, r_{t,k}]`
as the pair `(ℓ, r)`. The height is `H = J.length` and the leaf profile is `n_t = |row t|`. -/
abbrev IntervalData : Type := List (List (ℤ × ℤ))

namespace IntervalData

/-- The leaf profile `(n₁, …, n_H)` of the interval data. -/
def counts (J : IntervalData) : List ℕ := J.map List.length

/-- The interval row of depth `t` (empty for `t = 0`, `t > H`). -/
def row (J : IntervalData) (t : ℕ) : List (ℤ × ℤ) :=
  if t = 0 then [] else J.getD (t - 1) []

/-- "Intervals as above" (A.1, p. 39): every interval has integer endpoints and width at most
one (`ℓ ≤ r ≤ ℓ + 1`), and at each depth both endpoint lists are nondecreasing. -/
def IsIntervalSystem (J : IntervalData) : Prop :=
  ∀ r ∈ J, (∀ p ∈ r, p.1 ≤ p.2 ∧ p.2 ≤ p.1 + 1) ∧
    (r.map Prod.fst).Pairwise (· ≤ ·) ∧ (r.map Prod.snd).Pairwise (· ≤ ·)

/-- The tree `T` respects the intervals: every sorted leaf coordinate `z_{t,k}(T)` lies in
`[ℓ_{t,k}, r_{t,k}]`. -/
def Respects (J : IntervalData) (T : OTree) : Prop :=
  ∀ t ∈ Finset.Icc 1 J.length,
    List.Forall₂ (fun (p : ℤ × ℤ) (z : ℕ) => p.1 ≤ (z : ℤ) ∧ (z : ℤ) ≤ p.2) (J.row t)
      (T.leafCoords t)

/-- The coefficients of the proof of Lemma A.1: `g_{t,k} = -2^{H-t}(ℓ_{t,k} + r_{t,k} + H - t)`,
as the depth-`t` row. -/
def gRow (J : IntervalData) (t : ℕ) : List ℤ :=
  (J.row t).map fun p => -(2 : ℤ) ^ (J.length - t) * (p.1 + p.2 + ((J.length - t : ℕ) : ℤ))

/-- `S* = ∑_{t=0}^{H-1} I_t 2^{H-t-1} (H - t)`, with `I_t` the internal counts of the profile. -/
def Sstar (J : IntervalData) : ℤ :=
  ∑ t ∈ Finset.range J.length,
    intCount J.counts t * 2 ^ (J.length - t - 1) * ((J.length - t : ℕ) : ℤ)

/-- The constant `Q₀ = -S* - ∑_{t,k} 2^{H-t} ℓ_{t,k} r_{t,k}` of the proof of Lemma A.1. -/
def Q0 (J : IntervalData) : ℤ :=
  -J.Sstar - ∑ t ∈ Finset.Icc 1 J.length,
    ((J.row t).map fun p => (2 : ℤ) ^ (J.length - t) * p.1 * p.2).sum

/-- The linear score `Q(T) = ∑_{t,k} g_{t,k} z_{t,k}(T)`. -/
def Q (J : IntervalData) (T : OTree) : ℤ :=
  ∑ t ∈ Finset.Icc 1 J.length,
    (List.zipWith (fun (g : ℤ) (z : ℕ) => g * (z : ℤ)) (J.gRow t) (T.leafCoords t)).sum

/-- The weighted interval penalty `∑_{t,k} 2^{H-t} (z_{t,k} - ℓ_{t,k})(z_{t,k} - r_{t,k})`. -/
def penalty (J : IntervalData) (T : OTree) : ℤ :=
  ∑ t ∈ Finset.Icc 1 J.length,
    (List.zipWith (fun (p : ℤ × ℤ) (z : ℕ) =>
      (2 : ℤ) ^ (J.length - t) * ((z : ℤ) - p.1) * ((z : ℤ) - p.2)) (J.row t)
      (T.leafCoords t)).sum

end IntervalData

end UnequalHuffman.NPC


