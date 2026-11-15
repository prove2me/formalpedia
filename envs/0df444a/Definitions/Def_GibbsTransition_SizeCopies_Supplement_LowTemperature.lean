-- Prove2me | Definitions.Def_GibbsTransition_SizeCopies_Supplement_LowTemperature
-- name    : GibbsTransition_SizeCopies_Supplement_LowTemperature
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:38:26.601207+00:00
-- url     : https://prove2.me/theorems/a81b4204-0fbf-4606-8268-6d9de82d0110
-- title:
--   The explicit larger-system Gibbs learner at confidence one tenth
-- statement:
--   On the published class, the finite-temperature local learner uses the same rational interval updates, confidence allocation and empirical comparison as the ground learner, but it samples fresh Gibbs states and chooses
--   $$L_k=\left\lceil\frac{32C}{d\gamma_k}\right\rceil,\qquad C=27/8,\quad d=1/2.$$
--   The module gives the exact product Born law of the single-site measurement on each independently supplied cube, its final rational output law, and its deterministic total supplied-spin count.
--
--   The factor $32$ is retained separately from the ground learner's factor $16$. Inverse temperature is a public fixed input to the entire run; it is not changed between queries.
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), Theorem 5.1 proof, (28), Section 3.1, printed pp. 6,9 (PDF pp. 8,11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Supplement_GroundLearner
set_option autoImplicit false

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace GibbsTransition.SizeCopies.Supplement
attribute [local instance] Classical.propDecidable

/-- The factor 32, rather than the ground learner's 16, is the source's
finite-temperature comparison size. Every query is still a fresh cube. -/
def largeGibbsSide (k : ℕ) : ℕ :=
  ⌈32*surfaceC starData/(gap starData*roundMargin k)⌉₊

def localGibbsMean (u : Interaction) (beta : ℚ) (L : ℕ) (phi : ℚ) : ℝ :=
  (L : ℝ)⁻¹^3 * ∑ x : Site L,
    (Matrix.trace (gibbsDensity u L phi beta * atSite publicP x)).re

def largeGibbsStep (u : Interaction) (beta epsilon delta : ℚ)
    (h : List Bool) : Measure (List Bool) :=
  let k := h.length
  let n := groundCount starData epsilon delta k
  let m := localGibbsMean u beta (largeGibbsSide k) (historyField h k)
  ∑ y : Fin n → Bool, (∏ i : Fin n, sampleBitWeight m (y i)) •
    Measure.dirac (h ++ [comparison ((starData.a+starData.b)/2) y])

def largeGibbsRun (u : Interaction) (beta epsilon delta : ℚ) : ℕ → Measure (List Bool)
  | 0 => Measure.dirac []
  | k+1 => (largeGibbsRun u beta epsilon delta k).bind (largeGibbsStep u beta epsilon delta)

def largeGibbsFinal (u : Interaction) (beta epsilon delta : ℚ) : Measure ℚ :=
  Measure.map groundOutput (largeGibbsRun u beta epsilon delta (groundRounds epsilon))

def largeGibbsSpins (epsilon delta : ℚ) : ℕ :=
  ∑ k ∈ Finset.range (groundRounds epsilon),
    groundCount starData epsilon delta k * (largeGibbsSide k)^3

end GibbsTransition.SizeCopies.Supplement


