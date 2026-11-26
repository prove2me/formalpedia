-- Prove2me | Definitions.Def_BicausalOT_SemianalyticValue
-- name    : BicausalOT_SemianalyticValue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:11:24.916799+00:00
-- url     : https://prove2.me/theorems/a413c1a2-c19d-501c-956c-2a641a9cc7a9
-- title:
--   Semianalytic Value
-- statement:
--   Definitions and structural lemmas for Semianalytic Value, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/SemianalyticValue.lean

import Definitions.Def_BicausalOT_MultiPeriodTopology
import Definitions.Def_BicausalOT_FeasNonempty
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LsaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
def WeakP (W : Type*) [MeasurableSpace W] : Type _ := ProbabilityMeasure W
namespace WeakP
variable {W : Type*} [MeasurableSpace W] [TopologicalSpace W]
  [OpensMeasurableSpace W]
instance : TopologicalSpace (WeakP W) :=
  inferInstanceAs (TopologicalSpace (ProbabilityMeasure W))
instance : MeasurableSpace (WeakP W) := borel (WeakP W)
instance : BorelSpace (WeakP W) := ⟨rfl⟩
instance [PolishSpace W] [BorelSpace W] : PolishSpace (WeakP W) :=
  ProbabilityMeasure.instPolishSpace (X := W)
def toMeasure (γ : WeakP W) : Measure W :=
  ProbabilityMeasure.toMeasure γ
instance (γ : WeakP W) : IsProbabilityMeasure γ.toMeasure :=
  (γ : ProbabilityMeasure W).prop
end WeakP
namespace MultiPeriod
variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
variable (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
variable (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
def FeasGraph (t : ℕ) :
    Set (PairHist X Y t × WeakP (X (t + 1) × Y (t + 1))) :=
  {p | p.2.toMeasure ∈ Feas κμ κν t p.1}
end MultiPeriod
end


