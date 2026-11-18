-- Prove2me | Definitions.Def_Kyprianou_Ch02_AbstractPoissonRandomMeasureV7
-- name    : Kyprianou_Ch02_AbstractPoissonRandomMeasureV7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T12:29:36.178921+00:00
-- url     : https://prove2.me/theorems/1cf43a6a-2368-40f7-973c-339f2d32d943
-- title:
--   Definition 2.3: arbitrary-space Poisson random measure predicate
-- statement:
--   An abstract Poisson random measure on any measurable space has measure-valued samples, measurable evaluations, Poisson finite and infinite intensity laws, and independent counts on disjoint sets. This restores the textbook's definition without requiring a particular point-family constructor.
-- source:
--   Kyprianou (2006) Definition 2.3, physical PDF p.24, original 2006 edition; repaired 17 November 2026

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

/-- Original Definition 2.3 as an abstract property of a random counting
measure: measurable count evaluations, Poisson finite and infinite intensity
laws, and independent counts on disjoint measurable sets. -/
noncomputable def IsAbstractPoissonRandomMeasureCh02
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) (N : Ω → Measure E) : Prop :=
    (∀ (A : Set E), MeasurableSet A →
       Measurable (fun ω => N ω A)) ∧
    (∀ (A : Set E), MeasurableSet A → m A < ⊤ →
       ∀ᵐ ω ∂P, ∃ n : ℕ, N ω A = n) ∧
    (∀ (A : Set E), MeasurableSet A → m A < ⊤ →
       P.map (fun ω => N ω A) =
         (ProbabilityTheory.poissonMeasure (m A).toNNReal).map
           (Nat.cast : ℕ → ENNReal)) ∧
    (∀ (A : Set E), MeasurableSet A → m A = ⊤ →
       ∀ᵐ ω ∂P, N ω A = ⊤) ∧
    (∀ {ι : Type} [Countable ι] (A : ι → Set E),
       (∀ i, MeasurableSet (A i)) →
       Pairwise (fun i j => Disjoint (A i) (A j)) →
       ProbabilityTheory.iIndepFun (fun i (ω : Ω) => N ω (A i)) P)

end Kyprianou.Ch02


