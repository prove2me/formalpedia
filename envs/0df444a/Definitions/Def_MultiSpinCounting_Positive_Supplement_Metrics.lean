-- Prove2me | Definitions.Def_MultiSpinCounting_Positive_Supplement_Metrics
-- name    : MultiSpinCounting_Positive_Supplement_Metrics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:22:21.883303+00:00
-- url     : https://prove2.me/theorems/66874c4b-d7fe-4b46-902b-56255ae35a45
-- title:
--   Finite total variation and Hilbert distance on a support
-- statement:
--   For real vectors $p,p'$ on a finite state space $\Omega$, total variation is
--   $$\operatorname{TV}(p,p')=\frac12\sum_{a\in\Omega}|p_a-p'_a|.$$
--   For a nonempty subset $S\subseteq\Omega$ on which both vectors are strictly positive, their supported Hilbert distance is
--   $$d_{H,S}(p,p')=\log\max_{a,b\in S}\frac{p_a p'_b}{p_b p'_a}.$$
--   The latter reuses the published Hilbert metric after bijectively labeling $S$ by a finite interval. Zero coordinates outside $S$ do not enter the maximum. These distances express the conclusions of Lemmas 2.1 and 5.6; normalization is imposed by those statements, rather than built into the vectors.
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), p. 3, 8, 22, Definition 1.1; (2.1); Lemma 5.6

import Mathlib
import Definitions.Def_CompOT_Sinkhorn_Defs

noncomputable section

namespace MultiSpinCounting.Positive.Supplement

/-- Total variation of finite real vectors, p. 3. -/
def tvDist {k : ℕ} (p p' : Fin k → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ a, |p a - p' a|

/-- (2.1) on the positive support only, via a bijection to Fin |S|.
Theorems require S nonempty and both vectors strictly positive there. -/
def supportHilbert {N : ℕ} (S : Finset (Fin N)) (p p' : Fin N → ℝ) : ℝ :=
  CompOT.Sinkhorn.hilbertMetric
    (fun i => p ((Fintype.equivFin S).symm i).val)
    (fun i => p' ((Fintype.equivFin S).symm i).val)

end MultiSpinCounting.Positive.Supplement


