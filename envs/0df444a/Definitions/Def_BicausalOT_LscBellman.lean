-- Prove2me | Definitions.Def_BicausalOT_LscBellman
-- name    : BicausalOT_LscBellman
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:29:34.240144+00:00
-- url     : https://prove2.me/theorems/32f1d65f-767b-5576-826d-4d907939ff55
-- title:
--   Lsc Bellman
-- statement:
--   Definitions and structural lemmas for Lsc Bellman, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace MultiPeriod
variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
variable (κμP : (t : ℕ) → XHist X t → ProbabilityMeasure (X (t + 1)))
variable (κνP : (t : ℕ) → YHist Y t → ProbabilityMeasure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
def stageMin (t : ℕ)
    (F : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) → ℝ≥0∞)
    (C : Set (WeakP (X (t + 1) × Y (t + 1)))) (h : PairHist X Y t) : ℝ≥0∞ :=
  ⨅ (γ : WeakP (X (t + 1) × Y (t + 1)))
    (_ : (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
      (fun t y => (κνP t y : Measure (Y (t + 1)))) t ∧ γ ∈ C), F (h, γ)
def argminSet (t : ℕ)
    (F : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) → ℝ≥0∞)
    (h : PairHist X Y t) : Set (WeakP (X (t + 1) × Y (t + 1))) :=
  {γ | (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
    (fun t y => (κνP t y : Measure (Y (t + 1)))) t ∧
    F (h, γ) ≤ stageMin κμP κνP t F univ h}
end MultiPeriod
end


