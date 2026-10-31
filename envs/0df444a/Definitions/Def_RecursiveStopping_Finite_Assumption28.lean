-- Prove2me | Definitions.Def_RecursiveStopping_Finite_Assumption28
-- name    : RecursiveStopping_Finite_Assumption28
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:40:25.723488+00:00
-- url     : https://prove2.me/theorems/c8240291-a19e-4139-9ff2-19f0e0c04bde
-- title:
--   Assumption 2.8: $F$ continuous on $[0,T]$
-- statement:
--   In the finite-horizon problem the distribution function $F(s)=\mu([0,s])$ of the delay is continuous on $[0,T]$, while $F(0)=\mu(\{0\})$ may be positive: the law of $\vartheta$ has no atom in $(0,T]$,
--
--   $$
--   \mu(\{s\})=0\qquad\text{for every }s\in(0,T].
--   $$
--
--   It is what makes the finite-horizon $\Lambda f$ continuous in the time coordinate.
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, Assumption 2.8, p.10

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace RecursiveStopping.Finite

/-- **Assumption 2.8** of Colaneri & De Angelis, arXiv:1905.02650v4, p.10: "In the finite-time
horizon problem we have `F` continuous on `[0, T]` with `F(0)` possibly strictly positive
(i.e., the law of `ϑ` may have an atom at zero)."

With `F(s) = μ([0, s])` the distribution function of the delay law `μ`, continuity of `F` on
`[0, T]` means that `μ` has no atom in `(0, T]` (`F` is always right-continuous, and continuity
within `[0, T]` at `0` is right-continuity). -/
def Assumption28 (μ : Measure ℝ≥0) (T : ℝ) : Prop :=
  ∀ s : ℝ≥0, 0 < s → (s : ℝ) ≤ T → μ {s} = 0

end RecursiveStopping.Finite


