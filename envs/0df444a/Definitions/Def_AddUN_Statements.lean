-- Prove2me | Definitions.Def_AddUN_Statements
-- name    : AddUN_Statements
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:21:35.985863+00:00
-- url     : https://prove2.me/theorems/337f6347-c3a5-4902-a6ec-0c513cfd4de0
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from VictorLiwentao (VictorLiwentao/open-logic-24-add-un; see pinned Apache-2.0 LICENSE and source headers)'s pinned Additivity of universally null sets and Goto Question 6.3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean

module
public import Definitions.Def_AddUN_UniversallyNull
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Cardinal MeasureTheory IdealInvariant Filter
namespace AddUN
scoped notation "𝒩" => Measure.nullSets cantorMeasure
scoped notation "𝒰𝒩" => universallyNullSets (ℕ → Bool)
noncomputable def dominatingNumber : Cardinal.{0} :=
  ⨅ D : {D : Set (ℕ → ℕ) // ∀ f, ∃ g ∈ D, f ≤ᶠ[atTop] g}, #D.1
def Question63 : Prop := add 𝒩 = add 𝒰𝒩
def GotoCor513 : Prop := add 𝒩 ≤ add 𝒰𝒩
def GotoProp54 : Prop := non 𝒰𝒩 = non 𝒩
def Grzegorek : Prop := ∃ A : Set (ℕ → Bool), IsUniversallyNull A ∧ #A = non 𝒩
def TheoremA : Prop := add 𝒰𝒩 ≤ dominatingNumber
def TheoremB : Prop :=
  ∀ A : Set (ℕ → Bool), IsUniversallyNull A → #A = cof 𝒩 → add 𝒰𝒩 = add 𝒩
def CorollaryA : Prop := non 𝒩 = cof 𝒩 → add 𝒰𝒩 = add 𝒩
def CorollaryB : Prop := (𝔠 : Cardinal.{0}) ≤ ℵ_ 2 → add 𝒰𝒩 = add 𝒩
def CorollaryC : Prop :=
  add 𝒩 < add 𝒰𝒩 →
    (ℵ_ 3 : Cardinal.{0}) ≤ 𝔠 ∧ non 𝒩 < cof 𝒩 ∧
      ∀ A : Set (ℕ → Bool), IsUniversallyNull A → #A < cof 𝒩
end AddUN


