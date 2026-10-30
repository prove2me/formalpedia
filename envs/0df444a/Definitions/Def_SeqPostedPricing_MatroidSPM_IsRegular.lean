-- Prove2me | Definitions.Def_SeqPostedPricing_MatroidSPM_IsRegular
-- name    : SeqPostedPricing_MatroidSPM_IsRegular
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:34:45.689406+00:00
-- url     : https://prove2.me/theorems/c658e306-5add-4120-871d-fda4a728a96b
-- title:
--   Regular distribution with density: virtual value $\phi(v)=v-\frac{1-F(v)}{f(v)}$ non-decreasing
-- statement:
--   A probability distribution $\nu$ on $\mathbb R$ with distribution function $F(x)=\nu((-\infty,x])$ is **regular** if it has a density $f\ge0$ such that
--
--   1. $f(x)>0$ at every $x$ with $0<F(x)<1$, and
--   2. the **virtual value**
--
--   $$
--   \phi(x)=x-\frac{1-F(x)}{f(x)}
--   $$
--
--   is monotone non-decreasing on $\{x: 0<F(x)<1\}$.
--
--   Regularity is the hypothesis under which Myerson's mechanism allocates by virtual values without ironing and under which the revenue bound of Lemma 2 holds.
--
--   **Formalization Note** The virtual value is undefined where $f=0$; it is read as $-\infty$ there, so a regular distribution has no density gap strictly inside its support (clause 1). Nothing else is assumed: values may be negative and supports unbounded.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.1, p. 4 (density); App. A, Definitions 1 and 2, p. 12

import Mathlib
open MeasureTheory

namespace SeqPostedPricing.MatroidSPM

/-- **Regular distribution with a density.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §2.1, p. 4 (PDF p. 6): values have "distribution function Fi with density fi"; App. A,
Definition 1, p. 12 (PDF p. 14): "φi(vi) = vi − (1 − Fi(vi))/fi(vi)"; Definition 2: "A one
dimensional distribution distribution F is regular, if φ(v) is monotone non-decreasing in v."

`IsRegular ν` holds when `ν` has a measurable density `f ≥ 0` with respect to Lebesgue measure,
`f > 0` at every point `x` with `0 < F(x) < 1` (where `F(x) = ν((−∞, x])`), and the virtual
value `φ(x) = x − (1 − F(x))/f(x)` is monotone non-decreasing on `{x | 0 < F(x) < 1}`.

**Formalization Note.** The virtual value is undefined where `f = 0`; it is read as `−∞` there,
so a regular distribution cannot have a density gap strictly inside its support, which is the
positivity clause. Without it Lean's `x / 0 = 0` would make `φ(x) = x` at such points. Nothing
else (continuity of `f`, bounded support, nonnegative values) is assumed. -/
def IsRegular (ν : Measure ℝ) : Prop :=
  ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
    ν = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
    (∀ x, 0 < (ν (Set.Iic x)).toReal → (ν (Set.Iic x)).toReal < 1 → 0 < f x) ∧
    MonotoneOn (fun x => x - (1 - (ν (Set.Iic x)).toReal) / f x)
      {x | 0 < (ν (Set.Iic x)).toReal ∧ (ν (Set.Iic x)).toReal < 1}

end SeqPostedPricing.MatroidSPM


