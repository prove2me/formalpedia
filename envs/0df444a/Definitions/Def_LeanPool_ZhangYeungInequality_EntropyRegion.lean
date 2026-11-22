-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_EntropyRegion
-- name    : LeanPool_ZhangYeungInequality_EntropyRegion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:51:15.985914+00:00
-- url     : https://prove2.me/theorems/4c8be644-4e2a-4ab7-8378-6cc587151ab1
-- title:
--   Entropy Region
-- statement:
--   Definitions and structural lemmas for Entropy Region, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/EntropyRegion.lean

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped Topology
universe u
def IFN {n : ℕ} (F : Finset (Fin n) → ℝ) (α β : Finset (Fin n)) : ℝ :=
  F α + F β - F (α ∪ β)
def condIFN {n : ℕ} (F : Finset (Fin n) → ℝ) (α β γ : Finset (Fin n)) : ℝ :=
  F (α ∪ γ) + F (β ∪ γ) - F (α ∪ β ∪ γ) - F γ
def deltaFN {n : ℕ} (F : Finset (Fin n) → ℝ) (i j k l : Fin n) : ℝ :=
  IFN F {i} {j} - condIFN F {i} {j} {k} - condIFN F {i} {j} {l}
def shannonConeN {n : ℕ} (F : Finset (Fin n) → ℝ) : Prop :=
  F ∅ = 0 ∧
  (∀ α β : Finset (Fin n), α ⊆ β → F α ≤ F β) ∧
  (∀ α β : Finset (Fin n), F (α ∪ β) + F (α ∩ β) ≤ F α + F β)
def zhangYeungAtN {n : ℕ} (F : Finset (Fin n) → ℝ) (i j k l : Fin n) : Prop :=
  deltaFN F i j k l ≤ (1 / 2) * (IFN F {k} {l} + IFN F {k} ({i} ∪ {j})
    + condIFN F {i} {j} {k} - condIFN F {i} {j} {l})
def zhangYeungHoldsN {n : ℕ} (F : Finset (Fin n) → ℝ) : Prop :=
  ∀ i j k l : Fin n, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    zhangYeungAtN F i j k l
noncomputable def entropyFnN
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {S : Fin n → Type u}
    [∀ i, MeasurableSpace (S i)]
    (X : ∀ i : Fin n, Ω → S i) (μ : Measure Ω) : Finset (Fin n) → ℝ :=
  fun α => H[(fun ω : Ω => fun i : α => X i.1 ω); μ]
noncomputable abbrev entropyFn
    {Ω : Type*} [MeasurableSpace Ω]
    {S : Fin 4 → Type u}
    [∀ i, MeasurableSpace (S i)]
    (X : ∀ i : Fin 4, Ω → S i) (μ : Measure Ω) : Finset (Fin 4) → ℝ :=
  entropyFnN X μ
def shannonRegionN (n : ℕ) : Set (Finset (Fin n) → ℝ) :=
  {F | shannonConeN F}
def entropyRegionN (n : ℕ) : Set (Finset (Fin n) → ℝ) :=
  {F | ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (S : Fin n → Type u) (_ : ∀ i, MeasurableSpace (S i)) (_ : ∀ i, Fintype (S i))
      (_ : ∀ i, MeasurableSingletonClass (S i))
      (X : ∀ i : Fin n, Ω → S i),
      (∀ i, Measurable (X i)) ∧ F = entropyFnN X μ}
def almostEntropicRegionN (n : ℕ) : Set (Finset (Fin n) → ℝ) :=
  closure (entropyRegionN.{u} n)
def restrictFirstFour {n : ℕ} (hn : 4 ≤ n) :
    (Finset (Fin n) → ℝ) → (Finset (Fin 4) → ℝ) :=
  fun F α => F (α.map (Fin.castLEEmb hn))
end ZhangYeung


