-- Prove2me | Definitions.Def_RecoveringBandits_supp
-- name    : RecoveringBandits_supp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:53:28.333249+00:00
-- url     : https://prove2.me/theorems/9814af35-afb3-4992-bf5a-2521655d1fb7
-- title:
--   Supporting points $d^{(k)}_i$ of the concave envelope
-- statement:
--   For a recovery function $r=R_i$, the **supporting points** are defined inductively by $d^{(0)}_i=0$ and, for $k\ge1$,
--
--   $$d^{(k)}_i=\min\Big(\operatorname*{arg\,max}_{d>d^{(k-1)}_i}\frac{r(d)-r(d^{(k-1)}_i)}{d-d^{(k-1)}_i}\Big).$$
--
--   They are the points where $r$ meets its upper concave envelope, and they form an infinite strictly increasing sequence. The long-run value $F_i$ has its nodes at $1/d^{(k)}_i$.
--
--   **Formalization Note** If the maximum over the infinite set $\{d>d^{(k-1)}_i\}$ were not attained, the definition falls back to $d^{(k-1)}_i+1$. For an admissible arm the maximum is always attained (the slopes are non-negative and tend to $0$), so the fallback never triggers; when the maximum is $0$ the least maximizer is $d^{(k-1)}_i+1$, which is the paper's own convention.
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, §4.1, p.10 (and p.11, first line)

import Mathlib

namespace RecoveringBandits

/-- The slope `(r(d) − r(p)) / (d − p)` of the chord from `p` to `d`
(arXiv:2106.14813v2, §4.1, p.10). Used only for `d > p`. -/
noncomputable def chordSlope (r : ℕ → ℝ) (p d : ℕ) : ℝ :=
  (r d - r p) / ((d : ℝ) - p)

/-- The next supporting point after `p`: the least maximizer over `d > p` of the chord slope
`(r(d) − r(p)) / (d − p)` (arXiv:2106.14813v2, §4.1, p.10).

**Formalization Note.** If the maximum over the infinite set `{d > p}` is not attained, the
fallback `p + 1` is used. Under `ArmAdmissible` the maximum is always attained (the slopes are
`≥ 0` and tend to `0`, p.10), so the fallback never triggers; when the maximum is `0`, every
`d > p` attains it and the least maximizer is `p + 1`, which is exactly the paper's
"Otherwise, `d^k_i = d^{(k−1)}_i + 1`" (p.11). -/
noncomputable def nextSupp (r : ℕ → ℝ) (p : ℕ) : ℕ := by
  classical
  exact if h : ∃ d, p < d ∧ ∀ d', p < d' → chordSlope r p d' ≤ chordSlope r p d
    then Nat.find h else p + 1

/-- **Supporting points `d^{(k)}_i`** (arXiv:2106.14813v2, §4.1, p.10): `d^{(0)}_i = 0` and, for
`k ≥ 1`,
`d^{(k)}_i = min (argmax_{d > d^{(k−1)}_i} (R_i(d) − R_i(d^{(k−1)}_i)) / (d − d^{(k−1)}_i))`.
They form an infinite strictly increasing sequence (p.11). -/
noncomputable def supp (r : ℕ → ℝ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => nextSupp r (supp r k)

end RecoveringBandits


