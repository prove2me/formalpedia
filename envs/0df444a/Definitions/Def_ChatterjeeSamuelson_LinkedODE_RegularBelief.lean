-- Prove2me | Definitions.Def_ChatterjeeSamuelson_LinkedODE_RegularBelief
-- name    : ChatterjeeSamuelson_LinkedODE_RegularBelief
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:44:05.841283+00:00
-- url     : https://prove2.me/theorems/56624172-1969-472f-85ed-ae7cb6c9517d
-- title:
--   Regular belief about the opponent's reservation price
-- statement:
--   In the bargaining model of Chatterjee and Samuelson each party knows its own reservation price and holds a subjective probability distribution over the opponent's. Let $[\underline v, \bar v]$ be the range of the opponent's reservation price.
--
--   A probability measure $\mu$ on $\mathbb R$ with distribution function $F(v) = \mu((-\infty, v])$ is a **regular belief** on $[\underline v, \bar v]$ with density $f$ if
--
--   1. $\underline v < \bar v$;
--   2. $F(\underline v) = 0$ and $F(\bar v) = 1$;
--   3. $F$ is strictly increasing on $[\underline v, \bar v]$;
--   4. $F$ is differentiable on $[\underline v, \bar v]$ with derivative $f(v)$ at each $v \in [\underline v, \bar v]$ (one-sided at the endpoints).
--
--   The buyer's belief about the seller's value, with distribution function $F_b$ and density $f_b$, is regular on the seller's range $[\underline v_s, \bar v_s]$; the seller's belief about the buyer's value, $F_s$ with density $f_s$, is regular on $[\underline v_b, \bar v_b]$. These are the only distributional assumptions of the paper.
--
--   **Formalization Note** The belief is a measure so that expected profits are integrals against it; $F$ is Mathlib's `cdf μ`. The condition $F(\underline v) = 0$ also rules out an atom at $\underline v$. The density $f$ is a parameter, pinned down on $[\underline v, \bar v]$ only.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), pp. 837–838 [PDF 3–4], §1 The Basic Model (assumption on F_b and F_s)

import Mathlib

open MeasureTheory ProbabilityTheory Set

namespace ChatterjeeSamuelson.LinkedODE

/-- A player's belief about the opponent's reservation price (Chatterjee & Samuelson,
*Bargaining under Incomplete Information*, Oper. Res. 31(5) 1983, §1, pp. 837–838
[PDF 3–4], unnumbered text: "the buyer regards v_s as a random variable possessing a
cumulative distribution function F_b(v_s) satisfying F_b(v̲_s) = 0 and F_b(v̄_s) = 1, and
which is strictly increasing and differentiable on [v̲_s, v̄_s]"; the seller's `F_s` on
`[v̲_b, v̄_b]` likewise).

`RegularBelief μ lo hi f` says: `μ` is a probability measure on `ℝ` whose distribution
function `F = cdf μ` satisfies `F lo = 0`, `F hi = 1`, is strictly increasing on
`[lo, hi]`, and has derivative `f v` (within `[lo, hi]`) at every `v ∈ [lo, hi]`; the
value interval is nondegenerate, `lo < hi`.

*Formalization Note.* The belief is a measure rather than a bare function so that
expected profits are integrals against it. `cdf μ lo = 0` also rules out an atom at `lo`.
`f` is the paper's density (`f_b`, `f_s`); it is pinned down on `[lo, hi]` only
(one-sided derivatives at the endpoints). `lo < hi` is implicit in the paper's
"strictly increasing on [v̲, v̄]" with `F(v̲) = 0 < 1 = F(v̄)`. -/
def RegularBelief (μ : Measure ℝ) (lo hi : ℝ) (f : ℝ → ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ lo < hi ∧ cdf μ lo = 0 ∧ cdf μ hi = 1 ∧
    StrictMonoOn (cdf μ) (Icc lo hi) ∧
    ∀ v ∈ Icc lo hi, HasDerivWithinAt (cdf μ) (f v) (Icc lo hi) v

end ChatterjeeSamuelson.LinkedODE


