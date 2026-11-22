-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_Test_Theorem4
-- name    : LeanPool_ZhangYeungInequality_Test_Theorem4
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T15:22:26.50501+00:00
-- url     : https://prove2.me/theorems/edbba31b-862c-4961-a8ed-c7c133e4b519
-- title:
--   Theorem4
-- statement:
--   Definitions and structural lemmas for Theorem4, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Test/Theorem4.lean

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem4
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Measure
public import Theorems.Thm_ZhangYeung_FWitness_eq_cast
public import Theorems.Thm_ZhangYeung_not_zhangYeungHolds_witness
public import Theorems.Thm_ZhangYeung_not_zhangYeungHolds_witness_n
public import Theorems.Thm_ZhangYeung_shannonCone_of_witness
public import Theorems.Thm_ZhangYeung_shannonCone_of_witness_n
public import Theorems.Thm_ZhangYeung_shannon_incomplete
public import Theorems.Thm_ZhangYeung_shannon_incomplete_ge_four
public import Theorems.Thm_ZhangYeung_theorem4
public import Theorems.Thm_ZhangYeung_theorem4_finite
public import Theorems.Thm_ZhangYeung_theorem4_ge_four
public import Theorems.Thm_ZhangYeung_theorem4_seqClosure
public import Theorems.Thm_ZhangYeung_zhangYeungHolds_of_entropy
public import Theorems.Thm_ZhangYeung_zhangYeungHolds_of_tendsto

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace ZhangYeungTest
open MeasureTheory ProbabilityTheory
open ZhangYeung
open scoped ZhangYeungPFR
universe u
section SetFunctionCalculus
example (F : Finset (Fin 4) → ℝ) (α β : Finset (Fin 4)) :
    IF F α β = F α + F β - F (α ∪ β) :=
  rfl
example (F : Finset (Fin 4) → ℝ) (α β γ : Finset (Fin 4)) :
    condIF F α β γ = F (α ∪ γ) + F (β ∪ γ) - F (α ∪ β ∪ γ) - F γ :=
  rfl
example (F : Finset (Fin 4) → ℝ) (i j k l : Fin 4) :
    deltaF F i j k l = IF F {i} {j} - condIF F {i} {j} {k} - condIF F {i} {j} {l} :=
  rfl
end SetFunctionCalculus
section Predicates
example (F : Finset (Fin 4) → ℝ) :
    shannonCone F ↔
      F ∅ = 0 ∧
      (∀ α β : Finset (Fin 4), α ⊆ β → F α ≤ F β) ∧
      (∀ α β : Finset (Fin 4), F (α ∪ β) + F (α ∩ β) ≤ F α + F β) :=
  Iff.rfl
example (F : Finset (Fin 4) → ℝ) (i j k l : Fin 4) :
    zhangYeungAt F i j k l ↔
      deltaF F i j k l ≤ (1 / 2) * (IF F {k} {l} + IF F {k} ({i} ∪ {j})
        + condIF F {i} {j} {k} - condIF F {i} {j} {l}) :=
  Iff.rfl
example (F : Finset (Fin 4) → ℝ) :
    zhangYeungHolds F ↔ ∀ π : Equiv.Perm (Fin 4), zhangYeungAt F (π 0) (π 1) (π 2) (π 3) :=
  Iff.rfl
end Predicates
section Witness
example : FWitnessℚ (∅ : Finset (Fin 4)) = 0 := rfl
example (S : Finset (Fin 4)) : FWitness S = (FWitnessℚ S : ℝ) :=
  FWitness_eq_cast S
end Witness
section MainStatements
example : shannonCone FWitness := shannonCone_of_witness
example : ¬ zhangYeungHolds FWitness := not_zhangYeungHolds_witness
example : ∃ F : Finset (Fin 4) → ℝ, shannonCone F ∧ ¬ zhangYeungHolds F :=
  shannon_incomplete
example
    {Ω : Type*} [MeasurableSpace Ω]
    {S : Fin 4 → Type u}
    [∀ i, MeasurableSpace (S i)] [∀ i, Finite (S i)]
    [∀ i, MeasurableSingletonClass (S i)]
    {X : ∀ i : Fin 4, Ω → S i} (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    zhangYeungHolds (entropyFn X μ) :=
  zhangYeungHolds_of_entropy hX μ
example :
    ∃ F : Finset (Fin 4) → ℝ,
      shannonCone F ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        {S : Fin 4 → Type u}
        [∀ i, MeasurableSpace (S i)] [∀ i, Finite (S i)]
        [∀ i, MeasurableSingletonClass (S i)]
        (X : ∀ i : Fin 4, Ω → S i) (_ : ∀ i, Measurable (X i)),
        F ≠ entropyFn X μ :=
  theorem4_finite
example :
    ∃ F : Finset (Fin 4) → ℝ,
      F ∈ shannonRegionN 4 ∧ F ∉ almostEntropicRegionN.{u} 4 :=
  theorem4.{u}
end MainStatements
section WitnessEvaluation
example : FWitnessℚ ({0} : Finset (Fin 4)) = 2 := by decide
example : FWitnessℚ ({1} : Finset (Fin 4)) = 2 := by decide
example : FWitnessℚ ({2} : Finset (Fin 4)) = 2 := by decide
example : FWitnessℚ ({3} : Finset (Fin 4)) = 2 := by decide
example : FWitnessℚ ({0, 1} : Finset (Fin 4)) = 4 := by decide
example : FWitnessℚ ({0, 2} : Finset (Fin 4)) = 3 := by decide
example : FWitnessℚ ({0, 3} : Finset (Fin 4)) = 3 := by decide
example : FWitnessℚ ({1, 2} : Finset (Fin 4)) = 3 := by decide
example : FWitnessℚ ({1, 3} : Finset (Fin 4)) = 3 := by decide
example : FWitnessℚ ({2, 3} : Finset (Fin 4)) = 3 := by decide
example : FWitnessℚ ({0, 1, 2} : Finset (Fin 4)) = 4 := by decide
example : FWitnessℚ ({0, 1, 3} : Finset (Fin 4)) = 4 := by decide
example : FWitnessℚ ({0, 2, 3} : Finset (Fin 4)) = 4 := by decide
example : FWitnessℚ ({1, 2, 3} : Finset (Fin 4)) = 4 := by decide
example : FWitnessℚ ({0, 1, 2, 3} : Finset (Fin 4)) = 4 := by decide
end WitnessEvaluation
section DownstreamUsage
example : ∃ F : Finset (Fin 4) → ℝ, shannonCone F ∧ ¬ zhangYeungHolds F :=
  shannon_incomplete
example {Ω : Type*} [MeasurableSpace Ω]
    {X : ∀ _ : Fin 4, Ω → Fin 2} (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    zhangYeungAt (entropyFn X μ) 0 1 2 3 :=
  zhangYeungHolds_of_entropy hX μ (Equiv.refl _)
end DownstreamUsage
section ClosureStretch
open scoped Topology
example {F_seq : ℕ → Finset (Fin 4) → ℝ} {F : Finset (Fin 4) → ℝ}
    (h_seq : ∀ k, zhangYeungHolds (F_seq k))
    (h_lim : ∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α))) :
    zhangYeungHolds F :=
  zhangYeungHolds_of_tendsto h_seq h_lim
example :
    ∃ F : Finset (Fin 4) → ℝ, shannonCone F ∧
      ∀ (F_seq : ℕ → Finset (Fin 4) → ℝ),
        (∀ k, zhangYeungHolds (F_seq k)) →
        (∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α))) →
        False :=
  theorem4_seqClosure
end ClosureStretch
section NExtensionStretch
example (n : ℕ) (hn : 4 ≤ n) :
    ∃ F : Finset (Fin n) → ℝ, shannonConeN F ∧ ¬ zhangYeungHoldsN F :=
  shannon_incomplete_ge_four n hn
example (n : ℕ) (hn : 4 ≤ n) :
    ∃ F : Finset (Fin n) → ℝ,
      F ∈ shannonRegionN n ∧ F ∉ almostEntropicRegionN.{u} n :=
  theorem4_ge_four.{u} n hn
example {n : ℕ} (hn : 4 ≤ n) : shannonConeN (FWitnessN hn) :=
  shannonCone_of_witness_n hn
example {n : ℕ} (hn : 4 ≤ n) : ¬ zhangYeungHoldsN (FWitnessN hn) :=
  not_zhangYeungHolds_witness_n hn
example (F : Finset (Fin 4) → ℝ) :
    shannonConeN F ↔ shannonCone F := Iff.rfl
example (F : Finset (Fin 4) → ℝ) (i j k l : Fin 4) :
    zhangYeungAtN F i j k l ↔ zhangYeungAt F i j k l := Iff.rfl
end NExtensionStretch
end ZhangYeungTest


