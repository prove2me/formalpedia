-- Prove2me | solution 1 for AtomicDecomposition.C1SmallBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:58:07.017073+00:00
-- url     : https://prove2.me/submissions/840d8490-94b4-404f-bbc4-7e2ba2216eee

import Definitions.Def_Tablet_ApproximationMetric
import Definitions.Def_Tablet_BBAssertion
import Definitions.Def_Tablet_SurgeryEta
import Definitions.Def_Tablet_C1SmallBall
import Definitions.Def_Tablet_EtaRepeats
import Definitions.Def_MetricSurgery_Solution
import Theorems.Thm_ApproximationMetric
import Theorems.Thm_BBAssertion
import Theorems.Thm_C1SmallBall
import Theorems.Thm_EtaRepeats
import Theorems.Thm_SurgeryEta

section
open Set Filter Finset MeasureTheory ENNReal
private theorem tablet_C1SmallBall {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) (k : ℕ) (hpw : IsPiecewiseGeodesicWith γ k) :
    morreyNorm (curveMeasure γ) ≤ 2 * (k : ℝ≥0∞)
    :=
  _root_.C1SmallBall γ k hpw
namespace AtomicDecomposition
end AtomicDecomposition
end

set_option autoImplicit false
open Set Filter Finset MeasureTheory ENNReal
open AtomicDecomposition
namespace AtomicDecomposition
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) (k : ℕ) (hpw : IsPiecewiseGeodesicWith γ k) :
    morreyNorm (curveMeasure γ) ≤ 2 * (k : ℝ≥0∞)
    :=
  tablet_C1SmallBall γ k hpw
end AtomicDecomposition
