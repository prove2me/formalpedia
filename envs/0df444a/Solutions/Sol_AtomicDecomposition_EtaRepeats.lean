-- Prove2me | solution 1 for AtomicDecomposition.EtaRepeats
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:58:27.884262+00:00
-- url     : https://prove2.me/submissions/8ee2db5d-01c5-4db4-b5aa-113a0de98ed0

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
private theorem tablet_EtaRepeats {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : Form1 E → ℝ) (F : PSFamily T)
    (m : ℕ) (hm : 0 < m) (Q : Finset E) (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C)
    (l : ℕ) (hl : 0 < l) :
    ∫ γ, (l : ℝ)⁻¹ * psi (m * l) Q ε C γ ∂(F.eta l)
      = ∫ γ, psi m Q ε C γ ∂(F.eta 1)
    :=
  _root_.EtaRepeats T F m hm Q ε C hε hC l hl
namespace AtomicDecomposition
end AtomicDecomposition
end

set_option autoImplicit false
open Set Filter Finset MeasureTheory ENNReal
open AtomicDecomposition
namespace AtomicDecomposition
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : Form1 E → ℝ) (F : PSFamily T)
    (m : ℕ) (hm : 0 < m) (Q : Finset E) (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C)
    (l : ℕ) (hl : 0 < l) :
    ∫ γ, (l : ℝ)⁻¹ * psi (m * l) Q ε C γ ∂(F.eta l)
      = ∫ γ, psi m Q ε C γ ∂(F.eta 1)
    :=
  tablet_EtaRepeats T F m hm Q ε C hε hC l hl
end AtomicDecomposition
