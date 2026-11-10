-- Prove2me | Definitions.Def_GreedyColoringLCA969_LowerBound_Distribution
-- name    : GreedyColoringLCA969_LowerBound_Distribution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T09:48:16.129055+00:00
-- url     : https://prove2.me/theorems/c6b122e8-48c0-4f81-ba7e-2186d4f76394
-- title:
--   Countable input laws, positive-mass support and deterministic success
-- statement:
--   Let $\mu$ be a measure on all finite represented graphs, with the discrete sigma-algebra. In applications it is a probability measure. Its support in this discrete space is
--
--   $$\operatorname{supp}(\mu)=\{R:\mu(\{R\})>0\}.$$
--
--   For a deterministic seed fixing $B=(A,r)$, its distributional success is $\mu\{R:r\text{ makes }A\text{ globally succeed on }R\}$. Only the represented graph is random in this expression; the tape has already been fixed.
--
--   There is no finite-support or common-size assumption. Countability ensures that the displayed support has full measure for a probability law, and that this event is measurable. The same definition applies to the standard and full-list graph-query interfaces.
--
--   Differences from the source:
--   - encoding: a law over finite graphs and its support → a probability law on all represented inputs and support defined by positive singleton mass; reason: this countable discrete space includes all sizes and orders without a finite-support restriction
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), Lemma 3.4, p.11 (PDF 12); Appendix A.2, pp.36–37 (PDF 37–38); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/969.pdf

import Definitions.Def_GreedyColoringLCA969_LowerBound_Performance

open scoped ENNReal
open MeasureTheory
open Classical

namespace GreedyColoringLCA969.LowerBound

/-- Discrete positive-mass support; no finite-support assumption is imposed. -/
def InSupport (μ : MeasureTheory.Measure Input) (R : Input) : Prop := 0 < μ {R}

/-- Only the graph is random: the operational rule and its tape are already fixed. -/
noncomputable def distributionalSuccess {m : OracleMode} (B : DeterministicLCA m)
    (μ : MeasureTheory.Measure Input) : ℝ≥0∞ :=
  μ {R | B.2 ∈ successEvent B.1 R.2}

end GreedyColoringLCA969.LowerBound


