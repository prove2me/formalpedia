-- Prove2me | Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
-- name    : BicausalOT_DescriptiveSetTheory_Capacitability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:01:20.263802+00:00
-- url     : https://prove2.me/theorems/75840c71-6e66-4ebf-acaa-a728a9399691
-- title:
--   Capacitability
-- statement:
--   Definitions and structural lemmas for Capacitability, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
def capBelow (β : ℕ → ℕ) : Set (ℕ → ℕ) := {σ | ∀ i, σ i ≤ β i}
def capBelowN (β : ℕ → ℕ) (n : ℕ) : Set (ℕ → ℕ) := {σ | ∀ i < n, σ i ≤ β i}
theorem capBelowN_zero (β : ℕ → ℕ) : capBelowN β 0 = univ := by
  ext σ; simp [capBelowN]
theorem capBelowN_eq_iUnion_update (β : ℕ → ℕ) (n : ℕ) :
    capBelowN β n = ⋃ k, capBelowN (Function.update β n k) (n + 1) := by
  ext σ
  simp only [mem_iUnion]
  constructor
  · intro hσ
    refine ⟨σ n, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · rw [Function.update_of_ne (by omega)]; exact hσ i h
    · subst h; simp [Function.update_self]
  · rintro ⟨k, hk⟩ i hi
    have := hk i (by omega)
    rwa [Function.update_of_ne (by omega)] at this
theorem monotone_capBelowN_update (β : ℕ → ℕ) (n : ℕ) :
    Monotone (fun k => capBelowN (Function.update β n k) (n + 1)) := by
  intro k k' hkk' σ hσ i hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
  · rw [Function.update_of_ne (by omega)]
    have := hσ i hi
    rwa [Function.update_of_ne (by omega)] at this
  · subst h
    have := hσ i (by omega)
    rw [Function.update_self] at this ⊢
    omega
def capTrunc (σ : ℕ → ℕ) (n : ℕ) : ℕ → ℕ := fun i => if i < n then σ i else 0
def capSeqs (β : ℕ → ℕ) (n : ℕ) : Set (ℕ → ℕ) :=
  {s | (∀ i < n, s i ≤ β i) ∧ ∀ i, n ≤ i → s i = 0}
variable {Z : Type*} [TopologicalSpace Z]
def capScheme (π : (ℕ → ℕ) → Z) (f : ℕ → ℕ) (n : ℕ) : Set Z :=
  closure (π '' PiNat.cylinder f n)
def capW (π : (ℕ → ℕ) → Z) (β : ℕ → ℕ) (n : ℕ) : Set Z :=
  ⋃ s ∈ capSeqs β n, capScheme π s n
def capBranch (π : (ℕ → ℕ) → Z) (σ : ℕ → ℕ) : Set Z := ⋂ n, capScheme π σ n
def capKernel (π : (ℕ → ℕ) → Z) : Set Z := ⋃ σ, capBranch π σ
def capR (π : (ℕ → ℕ) → Z) (β : ℕ → ℕ) (n : ℕ) : Set Z :=
  ⋃ σ ∈ capBelowN β n, capBranch π σ
theorem capR_zero (π : (ℕ → ℕ) → Z) (β : ℕ → ℕ) : capR π β 0 = capKernel π := by
  unfold capR capKernel
  rw [capBelowN_zero]
  ext z; simp
theorem capR_eq_iUnion_update (π : (ℕ → ℕ) → Z) (β : ℕ → ℕ) (n : ℕ) :
    capR π β n = ⋃ k, capR π (Function.update β n k) (n + 1) := by
  unfold capR
  rw [capBelowN_eq_iUnion_update]
  exact biUnion_iUnion _ _
theorem monotone_capR_update (π : (ℕ → ℕ) → Z) (β : ℕ → ℕ) (n : ℕ) :
    Monotone (fun k => capR π (Function.update β n k) (n + 1)) := fun _ _ hkk' =>
  biUnion_subset_biUnion_left (monotone_capBelowN_update β n hkk')
theorem cap_exists_ext {Z : Type*} [TopologicalSpace Z]
    (π : (ℕ → ℕ) → Z) (m : Set Z → ℝ≥0∞)
    (hsup : ∀ s : ℕ → Set Z, Monotone s → m (⋃ k, s k) = ⨆ k, m (s k))
    {c : ℝ≥0∞} {b : ℕ → ℕ} {n : ℕ} (hb : c < m (capR π b n)) :
    ∃ k, c < m (capR π (Function.update b n k) (n + 1)) := by
  have key : m (capR π b n) = ⨆ k, m (capR π (Function.update b n k) (n + 1)) := by
    rw [← hsup _ (monotone_capR_update π b n), ← capR_eq_iUnion_update]
  rw [key] at hb
  exact lt_iSup_iff.mp hb
def capAux {Z : Type*} [TopologicalSpace Z]
    (π : (ℕ → ℕ) → Z) (m : Set Z → ℝ≥0∞)
    (hsup : ∀ s : ℕ → Set Z, Monotone s → m (⋃ k, s k) = ⨆ k, m (s k))
    {c : ℝ≥0∞} (h0 : c < m (capKernel π)) :
    (n : ℕ) → {b : ℕ → ℕ // c < m (capR π b n)}
  | 0 => ⟨fun _ => 0, by rw [capR_zero]; exact h0⟩
  | n + 1 =>
    ⟨Function.update (capAux π m hsup h0 n).val n
        (cap_exists_ext π m hsup (capAux π m hsup h0 n).2).choose,
     (cap_exists_ext π m hsup (capAux π m hsup h0 n).2).choose_spec⟩
def capBound {Z : Type*} [TopologicalSpace Z]
    (π : (ℕ → ℕ) → Z) (m : Set Z → ℝ≥0∞)
    (hsup : ∀ s : ℕ → Set Z, Monotone s → m (⋃ k, s k) = ⨆ k, m (s k))
    {c : ℝ≥0∞} (h0 : c < m (capKernel π)) (n : ℕ) : ℕ :=
  (capAux π m hsup h0 (n + 1)).val n
open ProbabilityTheory
section KernelLemma
variable {X Y : Type*}
  [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
def capPad (n : ℕ) (b : Fin n → ℕ) : ℕ → ℕ :=
  fun i => if h : i < n then b ⟨i, h⟩ else 0
end KernelLemma
end


