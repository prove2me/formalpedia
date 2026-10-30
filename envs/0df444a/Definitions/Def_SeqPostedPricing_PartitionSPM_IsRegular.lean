-- Prove2me | Definitions.Def_SeqPostedPricing_PartitionSPM_IsRegular
-- name    : SeqPostedPricing_PartitionSPM_IsRegular
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:07:24.290011+00:00
-- url     : https://prove2.me/theorems/078f5fb6-1c2f-467b-bf94-93132c8bf1ae
-- title:
--   Regular distribution with a density
-- statement:
--   Let $\nu$ be a probability distribution on $\mathbb R$ with distribution function $F(x) = \nu((-\infty, x])$. Then $\nu$ is **regular** if it has a density $f \ge 0$ with respect to Lebesgue measure such that
--
--   1. $f(x) > 0$ at every $x$ with $0 < F(x) < 1$, and
--   2. the **virtual value**
--   $$
--   \varphi(x) = x - \frac{1 - F(x)}{f(x)}
--   $$
--   is monotone non-decreasing on $\{x : 0 < F(x) < 1\}$.
--
--   **Formalization Note** The paper defines $\varphi$ and calls $F$ regular when $\varphi$ is monotone non-decreasing. $\varphi$ is undefined where $f = 0$; reading it as $-\infty$ there, monotonicity forces a density that is positive strictly inside the support, which is condition 1.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, App. A, Definitions 1–2, p. 12 (PDF p. 14); §2.1, p. 4 (PDF p. 6)

import Mathlib

namespace SeqPostedPricing.PartitionSPM

open MeasureTheory in
/-- **Regular distribution with a density** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, App. A, Definitions 1–2, p. 12 = PDF p. 14:
"φi(vi) = vi − (1 − Fi(vi))/fi(vi)"; "A one dimensional distribution F is regular, if φ(v) is
monotone non-decreasing in v"; and §2.1, p. 4 = PDF p. 6: values have distribution `F_i` "with
density f_i"). A measure `ν` on `ℝ` is regular when it has a (measurable, nonnegative) density `f`
with respect to Lebesgue measure such that, writing `F x = ν((−∞, x])`, the density is positive at
every `x` with `0 < F x < 1` and the virtual value `φ(x) = x − (1 − F x)/f x` is monotone
non-decreasing on `{x | 0 < F x < 1}`.

**Formalization Note** Reading 2 of the mission. `φ` is undefined where `f = 0`; it is read as `−∞`
there, so monotonicity of `φ` forces a density version positive strictly inside the support (no
gaps) with `φ` monotone there. The positivity clause is that reading, not an added hypothesis; it
also keeps Lean's `x / 0 = 0` out of `φ`. -/
def IsRegular (ν : Measure ℝ) : Prop :=
  ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
    ν = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
    (∀ x, 0 < (ν (Set.Iic x)).toReal → (ν (Set.Iic x)).toReal < 1 → 0 < f x) ∧
    MonotoneOn (fun x => x - (1 - (ν (Set.Iic x)).toReal) / f x)
      {x | 0 < (ν (Set.Iic x)).toReal ∧ (ν (Set.Iic x)).toReal < 1}

end SeqPostedPricing.PartitionSPM


