-- Prove2me | Definitions.Def_BasisWeightLearning_Exact_Domain
-- name    : BasisWeightLearning_Exact_Domain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:19:52.815417+00:00
-- url     : https://prove2.me/theorems/1824bcf1-10af-42c1-9eee-689461185383
-- title:
--   The hidden-parameter interval and its measure
-- statement:
--   The hidden parameter ranges over the entire interval $\Theta=[0,1]$. A continuation function is a real-valued function on this interval. The measure is Lebesgue measure on the interval, implemented by pulling back real Lebesgue measure along the subtype inclusion. Thus equality of functions is equality on $[0,1]$, and endpoints remain in the domain. No parameter grid or finite-support restriction is introduced.
-- source:
--   Hao Zhang, Dynamic Learning and Decision Making via Basis Weight Vectors, Operations Research (2022), DOI 10.1287/opre.2021.2240, supplied PDF p. 13 (printed p. 13), §§3.3–4.1.

import Mathlib

namespace BasisWeightLearning.Exact
abbrev Theta := Set.Icc (0 : ℝ) 1
abbrev ValueFunction := Theta → ℝ
noncomputable def intervalMeasure : MeasureTheory.Measure Theta :=
  MeasureTheory.Measure.comap (fun x : Theta => (x : ℝ)) MeasureTheory.volume
end BasisWeightLearning.Exact


