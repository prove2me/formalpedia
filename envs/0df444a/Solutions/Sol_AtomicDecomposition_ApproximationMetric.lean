-- Prove2me | solution 1 for AtomicDecomposition.ApproximationMetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:55:44.828795+00:00
-- url     : https://prove2.me/submissions/b1322ded-6d3f-4edc-9e64-3dd21d46fc8f

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
private theorem tablet_ApproximationMetric {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] [Nonempty E]
    (hAK : MassSupFormulaStatement E) (hPS : PaoliniStepanovExistsStatement E)
    (GP : GeodesicPairing E)
    (T : MetricCurrent1 E) (hbdry : BoundaryZero T.toFun)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (γ : ℕ → ℕ → Curve E) (lam : ℕ → ℕ → ℝ),
      (∀ n : ℕ, ∀ i < n, 0 ≤ lam n i) ∧
      (∀ n : ℕ, ∀ i < n, IsClosedCurve (γ n i)) ∧
      (∀ n : ℕ, ∀ i < n, IsPiecewiseGeodesic (γ n i)) ∧
      (∀ ω : Form1 E, Tendsto (fun n : ℕ =>
          ∑ i ∈ Finset.range n, lam n i * (curveCurrent (γ n i) ω / (γ n i).len))
        atTop (nhds (T.toFun ω))) ∧
      (∀ n : ℕ, ∑ i ∈ Finset.range n, |lam n i|
          ≤ (1 + ε) * (massOfFunctional T.toFun).toReal) ∧
      (∀ n : ℕ, ∀ i < n,
          morreyNorm (curveMeasure (γ n i)) ≤ ENNReal.ofReal (2088 / ε ^ 2))
    :=
  _root_.ApproximationMetric hAK hPS GP T hbdry ε hε0 hε1
namespace AtomicDecomposition
end AtomicDecomposition
end

set_option autoImplicit false
open Set Filter Finset MeasureTheory ENNReal
open AtomicDecomposition
namespace AtomicDecomposition
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] [Nonempty E]
    (hAK : MassSupFormulaStatement E) (hPS : PaoliniStepanovExistsStatement E)
    (GP : GeodesicPairing E)
    (T : MetricCurrent1 E) (hbdry : BoundaryZero T.toFun)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (γ : ℕ → ℕ → Curve E) (lam : ℕ → ℕ → ℝ),
      (∀ n : ℕ, ∀ i < n, 0 ≤ lam n i) ∧
      (∀ n : ℕ, ∀ i < n, IsClosedCurve (γ n i)) ∧
      (∀ n : ℕ, ∀ i < n, IsPiecewiseGeodesic (γ n i)) ∧
      (∀ ω : Form1 E, Tendsto (fun n : ℕ =>
          ∑ i ∈ Finset.range n, lam n i * (curveCurrent (γ n i) ω / (γ n i).len))
        atTop (nhds (T.toFun ω))) ∧
      (∀ n : ℕ, ∑ i ∈ Finset.range n, |lam n i|
          ≤ (1 + ε) * (massOfFunctional T.toFun).toReal) ∧
      (∀ n : ℕ, ∀ i < n,
          morreyNorm (curveMeasure (γ n i)) ≤ ENNReal.ofReal (2088 / ε ^ 2))
    :=
  tablet_ApproximationMetric hAK hPS GP T hbdry ε hε0 hε1
end AtomicDecomposition
