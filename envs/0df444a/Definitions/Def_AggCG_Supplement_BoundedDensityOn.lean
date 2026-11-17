-- Prove2me | Definitions.Def_AggCG_Supplement_BoundedDensityOn
-- name    : AggCG_Supplement_BoundedDensityOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:19:48.658201+00:00
-- url     : https://prove2.me/theorems/56fe08f5-e253-4083-b1f6-7c825fb09af3
-- title:
--   Bounded-density probability laws on an interval
-- statement:
--   A probability law has density at most $\kappa$ on $[a,b]$ when it is supported on that interval and assigns every measurable set $S$ mass at most $\kappa\,\mathrm{Leb}(S)$.
--
--   This packages the independent bounded-density assumptions used by the smoothed linkage and minimum-cut theorems.
-- source:
--   Sharma, Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms, STOC 2027 submission (manuscript sha256 f7ea0248…), Theorem 3.3, p.4, PDF p.5; §E.4, p.33, PDF p.34

import Mathlib

namespace AggCG.Supplement

open MeasureTheory

/-- A law `ν` on `ℝ` is supported on `[a, b]` and has a Lebesgue density bounded by `κ`
(Sharma, *Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and
Learning Algorithms*, STOC 2027 submission (manuscript sha256 f7ea0248…), Theorem 3.3, p.4, PDF p.5:
"independently from [1, 2], with each density bounded by κ"; §E.4, p.33, PDF p.34: "supported on
[a, a + B] with densities at most κ").

**Formalization Note** "Density at most `κ`" is stated as `ν s ≤ κ · Leb(s)` for every measurable `s`,
which is equivalent to absolute continuity with a density bounded by `κ` almost everywhere. That `ν` is a
probability law is an instance argument at each use. -/
def BoundedDensityOn (ν : Measure ℝ) (κ a b : ℝ) : Prop :=
  ν (Set.Icc a b)ᶜ = 0 ∧ ∀ s : Set ℝ, MeasurableSet s → ν s ≤ ENNReal.ofReal κ * volume s

end AggCG.Supplement


