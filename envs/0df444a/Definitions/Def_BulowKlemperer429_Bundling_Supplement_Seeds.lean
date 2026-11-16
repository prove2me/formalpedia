-- Prove2me | Definitions.Def_BulowKlemperer429_Bundling_Supplement_Seeds
-- name    : BulowKlemperer429_Bundling_Supplement_Seeds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:37:26.284762+00:00
-- url     : https://prove2.me/theorems/9547a29e-4d68-4325-a1be-b4e07ff33cf2
-- title:
--   The two-item seed, the improved seed total and its intensity
-- statement:
--   The two-item seed item law puts probabilities $3/5,1/5,1/15,2/15$ on the values $0,1,2,3$. The improved seed total is $S_{\mathrm{seed}}=X+Y$ with $X,Y$ independent, $X$ equal to $0$ with probability $3/4$ and otherwise exponential with rate $1$, $Y$ equal to $0$ with probability $1/12$ and otherwise exponential with rate $4$. Its compound-Poisson intensity is
--   $$\nu(x)=\frac{e^{-x}-e^{-4x/3}+e^{-4x}-e^{-48x}}{x}\qquad(x>0).$$
--
--   These are the concrete instances of Section 5 used in Lemmas 5.2 and 5.4.
--
--   **Formalization Note** The laws live on $[0,\infty)$; the exponential laws are Mathlib's (rate parametrization) transported from $\mathbb R$. The intensity is a real function, used only for $x>0$.
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 17, §5.2 two-item seed; §5.3 pp. 17–18 (PDF pp. 18–19) improved seed and intensity (PDF p. 18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling.Supplement

/-- Section 5.2, p. 17: the two-item seed's item law, values `0, 1, 2, 3` with probabilities
`3/5, 1/5, 1/15, 2/15`. -/
noncomputable def seedItemLaw : Measure ℝ≥0 :=
  (3 / 5 : ℝ≥0∞) • Measure.dirac 0 + (1 / 5 : ℝ≥0∞) • Measure.dirac 1 +
    (1 / 15 : ℝ≥0∞) • Measure.dirac 2 + (2 / 15 : ℝ≥0∞) • Measure.dirac 3

/-- Section 5.3, p. 18: the first component `X`, zero with probability `3/4`, otherwise
exponential with rate `1`. -/
noncomputable def improvedSeedX : Measure ℝ≥0 :=
  (3 / 4 : ℝ≥0∞) • Measure.dirac 0 +
    (1 / 4 : ℝ≥0∞) • (ProbabilityTheory.expMeasure 1).map Real.toNNReal

/-- Section 5.3, p. 18: the second component `Y`, zero with probability `1/12`, otherwise
exponential with rate `4`. -/
noncomputable def improvedSeedY : Measure ℝ≥0 :=
  (1 / 12 : ℝ≥0∞) • Measure.dirac 0 +
    (11 / 12 : ℝ≥0∞) • (ProbabilityTheory.expMeasure 4).map Real.toNNReal

/-- Section 5.3, p. 18: the law of the prescribed seed total `S_seed = X + Y`, `X, Y`
independent. -/
noncomputable def improvedSeedLaw : Measure ℝ≥0 :=
  (improvedSeedX.prod improvedSeedY).map (fun z => z.1 + z.2)

/-- Section 5.3, p. 18: the compound-Poisson intensity
`ν(x) = (e^{−x} − e^{−4x/3} + e^{−4x} − e^{−48x}) / x` for `x > 0`. -/
noncomputable def intensity (x : ℝ) : ℝ :=
  (Real.exp (-x) - Real.exp (-(4 * x / 3)) + Real.exp (-(4 * x)) - Real.exp (-(48 * x))) / x

end BulowKlemperer429.Bundling.Supplement


