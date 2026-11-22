-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_Test_EntropyRegion
-- name    : LeanPool_ZhangYeungInequality_Test_EntropyRegion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T15:03:49.338476+00:00
-- url     : https://prove2.me/theorems/6809a912-1fce-45c4-9f4c-b1c38a9c114e
-- title:
--   Entropy Region
-- statement:
--   Definitions and structural lemmas for Entropy Region, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Test/EntropyRegion.lean

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem4
public import Definitions.Def_LeanPool_ZhangYeungInequality_EntropyRegion
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_ZhangYeung_restrictFirstFour_witness_n

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace ZhangYeungTest
open MeasureTheory ProbabilityTheory
open scoped Topology
open ZhangYeung
open scoped ZhangYeungPFR
universe u
section EntropyFunction
example {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {S : Fin n → Type u}
    [∀ i, MeasurableSpace (S i)] (X : ∀ i : Fin n, Ω → S i) (μ : Measure Ω) :
    entropyFnN X μ = fun α : Finset (Fin n) => H[(fun ω : Ω => fun i : α => X i.1 ω); μ] :=
  rfl
example {Ω : Type*} [MeasurableSpace Ω] {S : Fin 4 → Type u}
    [∀ i, MeasurableSpace (S i)] (X : ∀ i : Fin 4, Ω → S i) (μ : Measure Ω) :
    entropyFn X μ = entropyFnN X μ :=
  rfl
end EntropyFunction
section Regions
example (n : ℕ) : shannonRegionN n = {F | shannonConeN F} :=
  rfl
example (n : ℕ) : Set (Finset (Fin n) → ℝ) :=
  entropyRegionN.{u} n
example (n : ℕ) :
    almostEntropicRegionN.{u} n = closure (entropyRegionN.{u} n) :=
  rfl
example
    {Ω : Type u} [MeasurableSpace Ω]
    {n : ℕ} {S : Fin n → Type u}
    [∀ i, MeasurableSpace (S i)] [∀ i, Fintype (S i)]
    [∀ i, MeasurableSingletonClass (S i)]
    (X : ∀ i : Fin n, Ω → S i) (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    entropyFnN X μ ∈ entropyRegionN.{u} n := by
  exact
    ⟨Ω, inferInstance, μ, inferInstance, S, inferInstance, inferInstance,
      inferInstance, X, hX, rfl⟩
example {n : ℕ} (hn : 4 ≤ n) :
    restrictFirstFour hn = fun F α => F (α.map (Fin.castLEEmb hn)) :=
  rfl
example (F : Finset (Fin 4) → ℝ) :
    shannonConeN F ↔ shannonCone F :=
  Iff.rfl
end Regions
section Restriction
example {n : ℕ} (hn : 4 ≤ n) :
    restrictFirstFour hn (FWitnessN hn) = FWitness :=
  restrictFirstFour_witness_n hn
end Restriction
end ZhangYeungTest


