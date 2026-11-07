-- Prove2me | Definitions.Def_PathORAMCap_QLaw
-- name    : PathORAMCap_QLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:13.923801+00:00
-- url     : https://prove2.me/theorems/9ec4049d-5e4d-484f-9c7e-389eaafa2911
-- title:
--   Geometric-load trees: the law of $Q^{(Z)}_h$, its moments, and $a$, $c(k)$, $B_h$
-- statement:
--   Let $G$ satisfy $\mathbb P[G=k]=2^{-k-1}$ for $k\ge0$. An **independent geometric-load tree** of height $h$ (bucket levels) has mutually independent node loads distributed as $G$; $Q^{(Z)}_h$ is the number of blocks passed above its root by upward packing with capacity $Z$, and $Q^{(Z)}_0=0$. Its law satisfies
--
--   $$Q^{(Z)}_{h+1}\overset{d}{=}\bigl(G+Q^{(Z,0)}_h+Q^{(Z,1)}_h-Z\bigr)^+$$
--
--   with $G$ and the two child overflows independent. The paper's $Q_h$ is $Q^{(4)}_h$. The module also defines
--
--   1. the moment $\mathbb E[u^{Q^{(Z)}_h}]$ and the capped mean $\mathbb E[\min\{K,Q^{(Z)}_h\}]$;
--   2. for $u=7/5$: $a=1/(u^4(2-u))=3125/7203$, $c(k)=\sum_{g\ge0}2^{-g-1}(1-u^{g+k-4})^+$, and $B_h=\mathbb E[c(Q^{(0)}_h+Q^{(1)}_h)]$ with independent copies of $Q_h$.
--
--   These are the comparison objects of the capacity-four upper bound and the capacity-three lower bound.
--
--   **Formalization Note** $Q^{(Z)}_h$ is defined by its law through the recursion above (a `PMF ℕ` built with `PMF.bind`), which determines it from $Q_0=0$. Moments, $c(k)$ and $B_h$ are computed in $[0,\infty]$. $G$ is Mathlib's `geometricPMF` with parameter $1/2$, deprecated at this Mathlib revision in favour of a measure version; the deprecation warning is silenced.
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), Definition 4.2, p.14 (PDF p.17), eq. (15); (16), p.15 (PDF p.18); (32), p.31 (PDF p.34); (48), p.40 (PDF p.43)

import Mathlib

set_option autoImplicit false

open scoped ENNReal

namespace PathORAMCap

set_option linter.deprecated false in
/-- The law of the nonnegative geometric load `G`, `P[G = k] = 2^{−k−1}` for `k ≥ 0` ((15),
Definition 4.2, Chang, Au, *The Minimum Bucket Capacity for Reliable Path ORAM*, STOC 2027 submission
(manuscript sha256 1762f048…), p.14 (PDF p.17)): Mathlib's `geometricPMF` with success probability
`1/2`, `(1 − 1/2)^k · 1/2`.

**Formalization Note.** `geometricPMF` is deprecated in favour of the measure `geometricMeasure`
at this Mathlib revision; the PMF form is kept because the recursion below is a `PMF.bind`. -/
noncomputable def geomHalf : PMF ℕ :=
  ProbabilityTheory.geometricPMF (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num)

/-- The law of `Q^(Z)_h`, the number of blocks passed above the root of an independent
geometric-load tree of height `h` (`h` bucket levels) after upward packing with capacity `Z`
(Definition 4.2, p.14 (PDF p.17); (16), p.15 (PDF p.18); (48), p.40 (PDF p.43)):
`Q_0 = 0` and `Q_{h+1} =ᵈ (G + Q^(0)_h + Q^(1)_h − Z)⁺` with `G`, `Q^(0)_h`, `Q^(1)_h` independent.

**Formalization Note.** `Q^(Z)_h` is defined by its law through the recursion (16)/(48), which
determines it from `Q_0 = 0`; truncated subtraction on `ℕ` is the positive part. The paper's `Q_h` is
`QLaw 4 h` and its `Q^(3)_h` is `QLaw 3 h`. -/
noncomputable def QLaw (Z : ℕ) : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | h + 1 => geomHalf.bind fun g => (QLaw Z h).bind fun a => (QLaw Z h).bind fun b =>
      PMF.pure (g + a + b - Z)

/-- The exponential moment `E[u^{Q^(Z)_h}]`, computed in `ℝ≥0∞` (it may be infinite in general). -/
noncomputable def QMoment (Z h : ℕ) (u : ℝ) : ℝ≥0∞ :=
  ∑' k, QLaw Z h k * ENNReal.ofReal (u ^ k)

/-- The capped mean `E[min{K, Q^(Z)_h}]` ((49)–(50), p.40 (PDF p.43)), in `ℝ≥0∞`; it is at most `K`. -/
noncomputable def QCapMean (Z h K : ℕ) : ℝ≥0∞ :=
  ∑' k, QLaw Z h k * ((min K k : ℕ) : ℝ≥0∞)

/-- The constant `a = 1/(u⁴(2 − u))` of §4.4 with `u = 7/5` (p.31 (PDF p.34)); it equals `3125/7203`. -/
noncomputable def aConst : ℝ := 1 / ((7 / 5 : ℝ) ^ 4 * (2 - 7 / 5))

/-- The function `c(k) = Σ_{g≥0} 2^{−g−1} (1 − u^{g+k−4})⁺` of (32), p.31 (PDF p.34), with `u = 7/5`
and an integer exponent `g + k − 4`.

**Formalization Note.** Computed in `ℝ≥0∞` (each term is the `ofReal` of a nonnegative real), so the
series needs no summability side condition. -/
noncomputable def cFun (k : ℕ) : ℝ≥0∞ :=
  ∑' g : ℕ, ENNReal.ofReal (((2 : ℝ) ^ (g + 1))⁻¹ *
    max (1 - (7 / 5 : ℝ) ^ ((g : ℤ) + (k : ℤ) - 4)) 0)

/-- `B_h = E[c(Q^(0)_h + Q^(1)_h)]` of (32), p.31 (PDF p.34), with `Q^(0)_h, Q^(1)_h` independent
copies of `Q_h = Q^(4)_h`. -/
noncomputable def BFun (h : ℕ) : ℝ≥0∞ :=
  ∑' i, ∑' j, QLaw 4 h i * QLaw 4 h j * cFun (i + j)

end PathORAMCap


