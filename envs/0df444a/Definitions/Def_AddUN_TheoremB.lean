-- Prove2me | Definitions.Def_AddUN_TheoremB
-- name    : AddUN_TheoremB
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:22:34.394261+00:00
-- url     : https://prove2.me/theorems/dad18f6a-66b0-4504-964b-0ebaff3b9b5b
-- title:
--   Theorem B
-- statement:
--   Definitions and structural lemmas for Theorem B, from VictorLiwentao (VictorLiwentao/open-logic-24-add-un; see pinned Apache-2.0 LICENSE and source headers)'s pinned Additivity of universally null sets and Goto Question 6.3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremB.lean

module
public import Definitions.Def_AddUN_Localisation
public import Definitions.Def_AddUN_Transfer
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Set Filter Cardinal MeasureTheory IdealInvariant
namespace AddUN
def CodingLemma : Prop :=
  ∃ (h : ℕ → ℕ) (φ : (ℕ → ℕ) → (ℕ → Bool) → (ℕ → Bool)),
    (∀ f, Measurable (φ f)) ∧
      ∀ K : Set (ℕ → Bool), IsCompact K → cantorMeasure K ≠ 0 → ∀ c : ℕ → Bool,
        ∃ S : ℕ → Finset ℕ, (∀ n, (S n).card ≤ h n) ∧
          ∀ f : ℕ → ℕ, (∃ᶠ n in atTop, f n ∉ S n) → ∃ w ∈ K, φ f w = c
end AddUN


