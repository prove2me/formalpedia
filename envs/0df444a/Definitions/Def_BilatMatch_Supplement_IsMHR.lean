-- Prove2me | Definitions.Def_BilatMatch_Supplement_IsMHR
-- name    : BilatMatch_Supplement_IsMHR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:26:57.506316+00:00
-- url     : https://prove2.me/theorems/9a2e086b-0840-41ef-a6ec-d18a53dbb4d5
-- title:
--   MHR buyer prior: density below the top of the support, nondecreasing hazard rate, possible top atom
-- statement:
--   A probability measure $\mu$ on $\mathbb R$ (a buyer's value prior, with CDF $F_B$) is **MHR** (monotone hazard rate) if it has a density $f_B$ below the upper endpoint $u$ of its support, possibly with an atom at $u$ when $u<\infty$, and the hazard rate
--   $$h(v)=\frac{f_B(v)}{1-F_B(v)}$$
--   is nondecreasing on the points below $u$ where $1-F_B(v)>0$, for some version of the density.
--
--   Precisely, for some measurable $f\ge0$, either $\mu=f\,dv$ on all of $\mathbb R$, or $\mu=\mu\{u\}\,\delta_u+f\,dv|_{(-\infty,u)}$ for some real $u$, with $v\mapsto f(v)/\mu((v,\infty))$ nondecreasing on the corresponding set. Deterministic priors are MHR. No positivity of the density, bounded support or finite mean is required.
--
--   This is the buyer class of the sharp MHR bounds (Theorem 4.1); clipping a buyer at an upper threshold keeps it MHR, which is why the top atom is allowed.
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490adbe231952acc5fc467ea7dfe37f237d7ce95248cd45c10451aedf4984), §4.1, p.17 (pdf p.19), definition of MHR buyers; deterministic priors p.41 (pdf p.43)

import Mathlib

open MeasureTheory

namespace BilatMatch.Supplement

/-- **MHR buyer prior** (Liu, Qin, Wang, *From Bilateral Trade to Matching Markets: Sharp Gains from
Trade*, arXiv:2609.30702, held version, sha256 ff1490ad…, §4.1, p.17 (pdf p.19): "Each original MHR
buyer distribution has a density `f_B` below the upper endpoint of its support, and its hazard rate
`f_B(v)/(1 − F_B(v))` is nondecreasing. An atom at the upper endpoint is allowed.").

`IsMHR μ`: `μ` is a probability measure on `ℝ` and, for some measurable nonnegative function `f`,
either
1. `μ` has density `f` on all of `ℝ` (no atom; support possibly unbounded above), and the hazard rate
   `f(v)/μ((v, ∞))` is nondecreasing on `{v | μ((v, ∞)) > 0}`; or
2. for some real `u`, `μ = μ{u}·δ_u + f·Lebesgue|_{(−∞, u)}` (density below `u`, a possible atom at
   `u`), and the hazard rate `f(v)/μ((v, ∞))` is nondecreasing on `{v < u | μ((v, ∞)) > 0}`.

**Formalization Note**
* `1 − F_B(v) = μ((v, ∞))`. The hazard rate is required to be monotone for some version `f` of the
  density, on the points where it is defined (positive survival, below the upper endpoint).
* A deterministic prior `δ_u` is MHR (case 2 with `f = 0`), as the paper uses (p.41). No positivity of
  the density, no bounded support and no finite mean are required.
* Case 1 covers supports unbounded above; a bounded support without a top atom is covered by both
  cases. -/
def IsMHR (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ ∃ f : ℝ → ℝ, Measurable f ∧ (∀ v, 0 ≤ f v) ∧
    ((μ = volume.withDensity (fun v => ENNReal.ofReal (f v)) ∧
        MonotoneOn (fun v => f v / (μ (Set.Ioi v)).toReal) {v | 0 < μ (Set.Ioi v)}) ∨
      ∃ u : ℝ, μ = μ {u} • Measure.dirac u +
          (volume.restrict (Set.Iio u)).withDensity (fun v => ENNReal.ofReal (f v)) ∧
        MonotoneOn (fun v => f v / (μ (Set.Ioi v)).toReal) {v | v < u ∧ 0 < μ (Set.Ioi v)})

end BilatMatch.Supplement


