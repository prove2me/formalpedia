-- Prove2me | solution 1 for AtomicDecomposition.BBAssertion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:55:54.547367+00:00
-- url     : https://prove2.me/submissions/768f4c1e-7d1c-48a4-9772-13d05bd3e825

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
private theorem tablet_BBAssertion {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] [Nonempty E]
    (hAK : MassSupFormulaStatement E) (hPS : PaoliniStepanovExistsStatement E)
    (GP : GeodesicPairing E)
    (T : MetricCurrent1 E) (hT0 : T.toFun ≠ 0) (hbdry : BoundaryZero T.toFun) :
    ∃ (n : ℕ → ℕ) (ghat : ℕ → ℕ → Curve E),
      (∀ l : ℕ, 0 < n l) ∧ Tendsto n atTop atTop ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, IsClosedCurve (ghat l i)) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, IsPiecewiseGeodesic (ghat l i)) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l,
        massOfFunctional (curveCurrent (ghat l i)) ≤ ENNReal.ofReal (ghat l i).len) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, (ghat l i).len ≤ 2 * (l : ℝ)) ∧
      (∀ ω : Form1 E, Tendsto (fun l : ℕ =>
          (massOfFunctional T.toFun).toReal / ((n l : ℝ) * l) *
            ∑ i ∈ Finset.range (n l), curveCurrent (ghat l i) ω)
          atTop (nhds (T.toFun ω))) ∧
      (Tendsto (fun l : ℕ => (1 / ((n l : ℝ) * l)) *
          ∑ i ∈ Finset.range (n l), (massOfFunctional (curveCurrent (ghat l i))).toReal)
        atTop (nhds 1)) ∧
      (Tendsto (fun l : ℕ => (1 / ((n l : ℝ) * l)) *
          ∑ i ∈ Finset.range (n l), (ghat l i).len)
        atTop (nhds 1))
    :=
  _root_.BBAssertion hAK hPS GP T hT0 hbdry
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
    (T : MetricCurrent1 E) (hT0 : T.toFun ≠ 0) (hbdry : BoundaryZero T.toFun) :
    ∃ (n : ℕ → ℕ) (ghat : ℕ → ℕ → Curve E),
      (∀ l : ℕ, 0 < n l) ∧ Tendsto n atTop atTop ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, IsClosedCurve (ghat l i)) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, IsPiecewiseGeodesic (ghat l i)) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l,
        massOfFunctional (curveCurrent (ghat l i)) ≤ ENNReal.ofReal (ghat l i).len) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, (ghat l i).len ≤ 2 * (l : ℝ)) ∧
      (∀ ω : Form1 E, Tendsto (fun l : ℕ =>
          (massOfFunctional T.toFun).toReal / ((n l : ℝ) * l) *
            ∑ i ∈ Finset.range (n l), curveCurrent (ghat l i) ω)
          atTop (nhds (T.toFun ω))) ∧
      (Tendsto (fun l : ℕ => (1 / ((n l : ℝ) * l)) *
          ∑ i ∈ Finset.range (n l), (massOfFunctional (curveCurrent (ghat l i))).toReal)
        atTop (nhds 1)) ∧
      (Tendsto (fun l : ℕ => (1 / ((n l : ℝ) * l)) *
          ∑ i ∈ Finset.range (n l), (ghat l i).len)
        atTop (nhds 1))
    :=
  tablet_BBAssertion hAK hPS GP T hT0 hbdry
end AtomicDecomposition
