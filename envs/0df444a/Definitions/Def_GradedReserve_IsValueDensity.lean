-- Prove2me | Definitions.Def_GradedReserve_IsValueDensity
-- name    : GradedReserve_IsValueDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:43.022858+00:00
-- url     : https://prove2.me/theorems/b64d6f93-d398-4187-8fd6-146d031fac91
-- title:
--   Value density on $[0,1]$, positive on $(0,1)$
-- statement:
--   A single item is sold to $n\ge2$ bidders whose private values $V_1,\dots,V_n$ are drawn independently from a distribution $F$ on $[0,1]$ with density $f$. The density is assumed to be
--
--   1. measurable,
--   2. nonnegative on $[0,1]$,
--   3. strictly positive on the open interval $(0,1)$, and
--   4. normalized: $\int_0^1 f(v)\,dv=1$.
--
--   These are the standing assumptions of the model; further smoothness is imposed only where a result needs it.
--
--   **Formalization Note** Values of $f$ outside $[0,1]$ are never used. Integrability on $[0,1]$ follows from the normalization.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 2, p.4 (PDF 5)

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The value law of Section 2 (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 2, p.4, PDF 5): values are drawn from a distribution
`F` on `[0, 1]` whose density `f` "is positive on (0, 1)". `IsValueDensity f` says that `f` is
measurable, nonnegative on `[0, 1]`, positive on `(0, 1)` and integrates to one over `[0, 1]`.

**Formalization Note.** The law is given by its density on `[0, 1]`; values of `f` outside
`[0, 1]` are never used (the type measure `typeMeasure f` restricts to `[0, 1]`). Nothing else is
assumed ("further smoothness is stated where it is used"). Integrability on `[0, 1]` follows from
the normalization, since a non-integrable function has interval integral `0 ≠ 1`. -/
def IsValueDensity (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ (∀ v ∈ Icc (0:ℝ) 1, 0 ≤ f v) ∧ (∀ v ∈ Ioo (0:ℝ) 1, 0 < f v) ∧
    ∫ v in (0:ℝ)..1, f v = 1

end GradedReserve


