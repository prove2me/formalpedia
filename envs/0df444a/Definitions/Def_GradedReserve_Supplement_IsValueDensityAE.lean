-- Prove2me | Definitions.Def_GradedReserve_Supplement_IsValueDensityAE
-- name    : GradedReserve_Supplement_IsValueDensityAE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:41:21.276401+00:00
-- url     : https://prove2.me/theorems/757c9a54-e678-4afa-a9bf-27264ba91555
-- title:
--   Value density positive almost everywhere on $(0,1)$ (Theorem 3.4)
-- statement:
--   Theorem 3.4 lets $F$ be absolutely continuous on $[0,1]$ with $f>0$ almost everywhere on $(0,1)$. A function $f$ is such a density when it is measurable, nonnegative almost everywhere on $[0,1]$, positive almost everywhere on $(0,1)$, and
--   $$\int_0^1 f(v)\,dv=1;$$
--   then $F(v)=\int_0^v f$.
--
--   This is weaker than the Section 2 assumption (density positive at every point of $(0,1)$) used elsewhere in the mission.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 3.4, p.7 (PDF 8); Section B conventions, p.25 (PDF 26)

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- The value law of Theorem 3.4 (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 3.4, p.7, PDF 8: "Let `F` be absolutely continuous
on `[0, 1]` with `f > 0` almost everywhere on `(0, 1)`"; Section B conventions, p.25, PDF 26):
`f` is a measurable density of `F` on `[0, 1]` — nonnegative almost everywhere on `[0, 1]`,
integrating to one — which is positive almost everywhere on `(0, 1)`.

**Formalization Note.** This is weaker than the base mission's `GradedReserve.IsValueDensity`
(positive at every point of `(0, 1)`). Absolute continuity of `F` is encoded by `F` having the
density `f`, as the base mission's `valueCdf f` does; values of `f` outside `[0, 1]` are never
used. -/
def IsValueDensityAE (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ (∀ᵐ v ∂volume, v ∈ Icc (0:ℝ) 1 → 0 ≤ f v) ∧
    (∀ᵐ v ∂volume, v ∈ Ioo (0:ℝ) 1 → 0 < f v) ∧ ∫ v in (0:ℝ)..1, f v = 1

end GradedReserve.Supplement


