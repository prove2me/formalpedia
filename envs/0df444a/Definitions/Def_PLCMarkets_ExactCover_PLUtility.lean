-- Prove2me | Definitions.Def_PLCMarkets_ExactCover_PLUtility
-- name    : PLCMarkets_ExactCover_PLUtility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T01:02:20.258648+00:00
-- url     : https://prove2.me/theorems/644eccc0-9ac0-4c96-b05f-d7bc58b91090
-- title:
--   Piecewise-linear concave utility function with an unbounded last piece (§2, §6)
-- statement:
--   A **piecewise-linear concave utility function** $f:\mathbb R_{\ge 0}\to\mathbb R_{\ge 0}$ with $f(0)=0$ is described by a finite list of bounded pieces $(c_1,a_1),\dots,(c_m,a_m)$ (slope, amount) followed by an unbounded last piece of slope $t$ (the *tail*). The function has slope $c_1$ on $[0,a_1]$, slope $c_2$ on $[a_1,a_1+a_2]$, and so on, and slope $t$ from $a_1+\dots+a_m$ to infinity:
--
--   $$
--   f(x)=\sum_{k=1}^m c_k\,\min\Big(\max\big(x-(a_1+\dots+a_{k-1}),0\big),\,a_k\Big)+t\,\max\Big(x-\sum_{k=1}^m a_k,\,0\Big).
--   $$
--
--   All data are rational. The listed slopes are positive, the amounts nonnegative, and the slopes are nonincreasing along the list and down to the tail, $c_1\ge c_2\ge\dots\ge c_m\ge t\ge 0$, so $f$ is nonnegative, nondecreasing and concave. A function that "goes flat" after its listed segments has $t=0$; a function that is flat everywhere has no listed segments and $t=0$. The **length** of $f$ is $a_1+\dots+a_m$.
--
--   These are the functions $f^i_j$ of Vazirani and Yannakakis: agent $i$'s utility for the amount of good $j$ he receives. The unbounded last piece is needed for the price-regulating agent of §8, whose utility has "slope 1 from then on until infinity".
--
--   **Formalization Note.** Listed segments have strictly positive slope; a zero-slope stretch is always represented by the tail $t=0$. This is a representation choice, not a restriction on the functions: every nondecreasing concave piecewise-linear function with $f(0)=0$ has such a representation. Negative arguments are evaluated as $0$.
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, p. 10:6 (§2, segments of f^i_j) and p. 10:10 (§6, first paragraph)

import Mathlib

namespace PLCMarkets.ExactCover

/-- A nonnegative, nondecreasing, concave, piecewise-linear utility function `f : ℝ₊ → ℝ₊` with
`f 0 = 0` and rational data (Vazirani–Yannakakis 2011, §2 p. 10:6 and §6 p. 10:10).

The pieces are listed from the origin: `segs = [(c₁, a₁), …, (c_m, a_m)]` means that `f` has
slope `c₁` on `[0, a₁]`, slope `c₂` on `[a₁, a₁ + a₂]`, and so on (a pair is `(slope, amount)`);
beyond `a₁ + ⋯ + a_m` the slope is `tail`, until infinity. A function that "goes flat" after its
listed segments has `tail = 0`. Listed slopes are positive, amounts nonnegative, and the slopes
are nonincreasing along the list and down to `tail` (concavity). -/
structure PLUtility where
  /-- The bounded pieces, as `(slope, amount)` pairs, in order from the origin. -/
  segs : List (ℚ × ℚ)
  /-- The slope of the last, unbounded piece (`0` = the function is flat from there on). -/
  tail : ℚ
  slope_pos : ∀ s ∈ segs, 0 < s.1
  amount_nonneg : ∀ s ∈ segs, 0 ≤ s.2
  tail_nonneg : 0 ≤ tail
  slope_antitone : segs.Pairwise (fun s t => t.1 ≤ s.1)
  tail_le : ∀ s ∈ segs, tail ≤ s.1

/-- Evaluation of the bounded pieces `segs` at `x` (negative `x` is treated as `0`):
`Σ_k c_k · min(max(x − a₁ − ⋯ − a_{k−1}, 0), a_k)`. -/
noncomputable def segEval : List (ℚ × ℚ) → ℝ → ℝ
  | [], _ => 0
  | (c, a) :: rest, x => (c : ℝ) * min (max x 0) (a : ℝ) + segEval rest (x - (a : ℝ))

/-- Total length `a₁ + ⋯ + a_m` of the bounded pieces. -/
def PLUtility.length (f : PLUtility) : ℚ := (f.segs.map Prod.snd).sum

/-- The value `f(x) = Σ_k c_k · min(max(x − a₁ − ⋯ − a_{k−1}, 0), a_k) + tail · max(x − Σ_k a_k, 0)`. -/
noncomputable def PLUtility.eval (f : PLUtility) (x : ℝ) : ℝ :=
  segEval f.segs x + (f.tail : ℝ) * max (x - (f.length : ℝ)) 0

/-- The identically zero ("flat", slope `0`) utility function. -/
def PLUtility.flat : PLUtility where
  segs := []
  tail := 0
  slope_pos := by simp
  amount_nonneg := by simp
  tail_nonneg := le_refl 0
  slope_antitone := List.Pairwise.nil
  tail_le := by simp

/-- One segment of slope `c > 0` and length `a ≥ 0`, followed by slope `t ∈ [0, c]` until
infinity. -/
def PLUtility.oneSeg (c a t : ℚ) (hc : 0 < c) (ha : 0 ≤ a) (ht : 0 ≤ t) (htc : t ≤ c) :
    PLUtility where
  segs := [(c, a)]
  tail := t
  slope_pos := by simpa using hc
  amount_nonneg := by simpa using ha
  tail_nonneg := ht
  slope_antitone := List.pairwise_singleton _ _
  tail_le := by simpa using htc

end PLCMarkets.ExactCover


