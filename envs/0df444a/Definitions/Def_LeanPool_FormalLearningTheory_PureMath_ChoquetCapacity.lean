-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ChoquetCapacity
-- name    : LeanPool_FormalLearningTheory_PureMath_ChoquetCapacity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:31:24.080307+00:00
-- url     : https://prove2.me/theorems/7d6969cf-334d-4c77-b396-3667b0a246af
-- title:
--   Choquet Capacity
-- statement:
--   Definitions and structural lemmas for Choquet Capacity, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ChoquetCapacity.lean

module
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open MeasureTheory Set Filter Topology
noncomputable def MeasureTheory.compactCap
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (s : Set α) : ENNReal :=
  sSup {r : ENNReal | ∃ K : Set α, IsCompact K ∧ K ⊆ s ∧ r = μ K}
structure MeasureTheory.IsChoquetCapacity
    {α : Type*} [TopologicalSpace α]
    (cap : Set α → ENNReal) : Prop where
  mono : ∀ {s t : Set α}, s ⊆ t → cap s ≤ cap t
  iUnion_nat : ∀ (f : ℕ → Set α), Monotone f →
    cap (⋃ n, f n) = ⨆ n, cap (f n)
  iInter_closed : ∀ (f : ℕ → Set α), Antitone f →
    (∀ n, IsClosed (f n)) →
    cap (⋂ n, f n) = ⨅ n, cap (f n)
abbrev Cyl (N : ℕ → ℕ) (n : ℕ) : Set (ℕ → ℕ) :=
  {g | ∀ i, i ≤ n → g i ≤ N i}
abbrev Bnd (N : ℕ → ℕ) : Set (ℕ → ℕ) :=
  {g | ∀ i, g i ≤ N i}
noncomputable def truncate (N : ℕ → ℕ) (g : ℕ → ℕ) : ℕ → ℕ :=
  fun i => min (g i) (N i)


