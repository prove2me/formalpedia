-- Prove2me | Definitions.Def_LocalDOvS_SUS_lookStep
-- name    : LocalDOvS_SUS_lookStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:26:34.107985+00:00
-- url     : https://prove2.me/theorems/9f34c814-3938-4c32-94ca-eb377fc7683b
-- title:
--   One test of the corrected algorithm (Type-I or Type-II)
-- statement:
--   One test of the corrected shrinking uniform sampling algorithm, made once every active point has $n=n(M)$ outputs, $M=|S|$. With $\hat F(x)$ the mean of these outputs and $h=h(n,\sigma,\alpha)$:
--
--   1. if there are $x\ne y$ in $S$ with $\hat F(x)+h\le\hat F(y)-h$, a Type-I Operation is made on such a pair, chosen by an arbitrary rule that sees only the outputs observed so far;
--   2. otherwise a Type-II Operation is made.
--
--   **Formalization Note** The printed line 10 tests condition (i) after every sample. Repeated testing at a fixed confidence level voids the guarantee: for $N=3$, Gaussian noise, $f=(0,2\epsilon,4\epsilon)$ and small $\epsilon$ a wrong separation occurs with probability near $1/2$. The test is made once per active-set size, when every half-width is at most $|S|\epsilon/80$ (condition (ii)); this is the first correction. If the rule's pair is not a valid Type-I pair, some valid pair is used.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Algorithm 2, lines 4–20, p.15 (line 10 corrected)

import Mathlib
import Definitions.Def_LocalDOvS_SUS_actSet
import Definitions.Def_LocalDOvS_SUS_typeIUpdate
import Definitions.Def_LocalDOvS_SUS_typeIIUpdate
import Definitions.Def_LocalDOvS_SUS_sampleMean
import Definitions.Def_LocalDOvS_SUS_halfWidth
import Definitions.Def_LocalDOvS_SUS_nLook

open scoped NNReal

namespace LocalDOvS.SUS

open Classical in
/-- One test of the corrected shrinking uniform sampling algorithm, made once every active point
has `n := n(M)` outputs, `M = |S|` (Zhang–Zheng–Lavaei, arXiv:2012.02427v2, Algorithm 2,
lines 4–20, p.15, corrected). `D x j` is the `(j + 1)`-th output of `x`. With
`F̂(x)` the mean of the first `n` outputs of `x` and `h := h(n, σ, α)`:

* if there are `x ≠ y` in `S` with `F̂(x) + h ≤ F̂(y) − h`, a Type-I Operation is made on such
  a pair, namely on `pick st' D'` when that is such a pair, and otherwise on some such pair;
* otherwise a Type-II Operation is made.

Here `st'` records that the points of `S` now have `n` outputs, and `D'` is `D` restricted to
the outputs seen so far (`D' x j = D x j` for `j < st'.cnt x`, else `0`), so `pick` is an
arbitrary rule using only the information available at this test.

**Formalization Note (correction).** The printed line 10 tests condition (i) after every
sample, at a fixed confidence level per comparison; this repeated testing voids the guarantee
(counterexample: `N = 3`, Gaussian noise, `f = (0, 2ε, 4ε)`, small `ε`). The test is made
once, when every active half-width is at most `|S| · ε/80` (condition (ii)), which is the
correction. Points are indexed by their position `j < M` in `S`. -/
noncomputable def lookStep (N : ℕ) (σ : ℝ≥0) (ε δ : ℝ)
    (pick : SUSState → (ℕ → ℕ → ℝ) → ℕ × ℕ) (D : ℕ → ℕ → ℝ) (st : SUSState) : SUSState :=
  let n := nLook N σ ε δ st.M
  let hw := halfWidth σ (alphaSUS N δ) n
  let st' : SUSState := { st with cnt := fun x => if x ∈ actSet st then n else st.cnt x }
  let D' : ℕ → ℕ → ℝ := fun x j => if j < st'.cnt x then D x j else 0
  let m : ℕ → ℝ := fun j => sampleMean D (st.x0 + j * st.s) n
  let valid : ℕ × ℕ → Prop := fun p =>
    p.1 < st.M ∧ p.2 < st.M ∧ p.1 ≠ p.2 ∧ m p.1 + hw ≤ m p.2 - hw
  if hI : ∃ p, valid p then
    let p := if valid (pick st' D') then pick st' D' else Classical.choose hI
    typeIUpdate st' p.1 p.2
  else
    typeIIUpdate st'

end LocalDOvS.SUS


