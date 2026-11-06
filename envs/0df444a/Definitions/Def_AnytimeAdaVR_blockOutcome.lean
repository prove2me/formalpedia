-- Prove2me | Definitions.Def_AnytimeAdaVR_blockOutcome
-- name    : AnytimeAdaVR_blockOutcome
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:23.5062+00:00
-- url     : https://prove2.me/theorems/af1c1a67-c464-4702-80c8-60f458991366
-- title:
--   Outcome of one block: endpoint, count $m$, stored candidate $y$
-- statement:
--   For a block with estimates $v_1,\dots,v_b$ and threshold $4a\sqrt{2/b}$, the **outcome** consists of:
--
--   1. the endpoint $x_{b+1}$, from which the next block starts;
--   2. the number $m$ of large estimates, $\|v_t\|>4a\sqrt{2/b}$;
--   3. the candidate $y=x_t$ for the first index $t>b/2$ with $\|v_t\|\le4a\sqrt{2/b}$ (absent if there is none).
--
--   The block succeeds if $m\ge b/2$ and fails otherwise; a failed block always has such a $t$, and its $y$ becomes the stored point $Y$.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), §5.1, eq. (12), p.7; Algorithm 2, lines 13–23, p.8

import Mathlib
import Definitions.Def_AnytimeAdaVR_blockSeq

namespace AnytimeAdaVR

/-- **The outcome of one S or M block.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), §5.1, p.7, (12) and "Reporting through unfinished
blocks", and Algorithm 2, lines 13–23, p.8: "Let m count the estimates satisfying ‖v_t‖ > 4a√(2/b).
A block is successful when m ≥ b/2. … A failed block has an index t > b/2 with ‖v_t‖ ≤ 4a√(2/b).
When that block finishes, store the first such pre-update point as Y."

`blockOutcome k g x a b ξ = (x_{b+1}, m, y)`: the endpoint from which the next block starts, the
number `m` of indices `1 ≤ t ≤ b` with `‖v_t‖ > 4a√(2/b)`, and `y = some x_t` for the first
`t > b/2` with `‖v_t‖ ≤ 4a√(2/b)` (`none` if there is no such `t`, Algorithm 2's `y = ⊥`).

**Formalization Note.** The iterates are those of `AnytimeAdaVR.blockSeq`; `x_t` is the second
component of `blockSeq … t`, the point at which estimate `t` was formed. -/
noncomputable def blockOutcome {d : ℕ} {Ξ : Type*} (k : SMKind)
    (g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (a : ℝ) (b : ℕ) (ξ : ℕ → Ξ) :
    EuclideanSpace ℝ (Fin d) × ℕ × Option (EuclideanSpace ℝ (Fin d)) :=
  let st := blockSeq k g x a b ξ
  let thr : ℝ := 4 * a * Real.sqrt (2 / (b : ℝ))
  let m := ((Finset.Icc 1 b).filter (fun t => thr < ‖(st t).2.2‖)).card
  let y := ((List.range' (b / 2 + 1) (b - b / 2)).find?
      (fun t => decide (‖(st t).2.2‖ ≤ thr))).map (fun t => (st t).2.1)
  ((st b).1, m, y)

end AnytimeAdaVR


