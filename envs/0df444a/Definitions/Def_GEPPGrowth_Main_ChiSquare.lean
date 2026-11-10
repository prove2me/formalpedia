-- Prove2me | Definitions.Def_GEPPGrowth_Main_ChiSquare
-- name    : GEPPGrowth_Main_ChiSquare
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T23:35:01.991665+00:00
-- url     : https://prove2.me/theorems/893f9549-26b7-4ff1-b507-c0335dfb32c1
-- title:
--   Definition 4.7 — real chi-square law
-- statement:
--   For a positive integer $k$, the chi-square law with $k$ degrees of freedom is the pushforward of $k$ independent standard real Gaussian coordinates under their squared Euclidean length:
--
--   $$\chi_k^2=\operatorname{Law}\!\left(\sum_{j=1}^k Z_j^2\right),\qquad Z_j\overset{\mathrm{iid}}\sim N(0,1).$$
--
--   This law supports every real moment in Lemma 4.8. The definition also assigns a point mass at zero when $k=0$; every source moment theorem restricts to $k>0$.
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Definition 4.7, printed p.9, PDF p.10

import Definitions.Def_GEPPGrowth_Main_Gaussian
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Definition 4.7, including an unused zero-degree total extension. -/
noncomputable def chiSquare (k : ℕ) : Measure ℝ :=
  (Measure.pi (fun _ : Fin k => gaussianReal 0 1)).map (fun x => ∑ i, x i ^ 2)

instance chiSquare_isProbabilityMeasure (k : ℕ) : IsProbabilityMeasure (chiSquare k) := by
  unfold chiSquare
  apply Measure.isProbabilityMeasure_map
  apply Measurable.aemeasurable
  fun_prop

end GEPPGrowth.Main


