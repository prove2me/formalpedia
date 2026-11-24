-- Prove2me | Definitions.Def_FltRegular_CaseI_Statement
-- name    : FltRegular_CaseI_Statement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:33:35.378807+00:00
-- url     : https://prove2.me/theorems/b1626190-f418-44fc-879c-105c0b8c7c2c
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from leanprover-community/flt-regular contributors (see pinned LICENSE and source headers)'s pinned Fermat's Last Theorem for regular primes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseI/Statement.lean

module
public import Mathlib.NumberTheory.FLT.Three
public import Definitions.Def_FltRegular_MayAssume_Lemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CaseI
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CyclRat
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Finset Nat IsCyclotomicExtension Ideal Polynomial Int Basis FltRegular.CaseI
open scoped NumberField
namespace FltRegular
variable {p : ℕ}
namespace CaseI
def SlightlyEasier : Prop :=
  ∀ ⦃a b c : ℤ⦄ {p : ℕ} [Fact p.Prime], IsRegularPrime p → 5 ≤ p →
    ({a, b, c} : Finset ℤ).gcd id = 1 → ¬a ≡ b [ZMOD p] → ¬↑p ∣ a * b * c →
    a ^ p + b ^ p ≠ c ^ p
def Statement : Prop :=
  ∀ ⦃a b c : ℤ⦄ {p : ℕ} [Fact p.Prime], IsRegularPrime p → ¬↑p ∣ a * b * c →
    a ^ p + b ^ p ≠ c ^ p
end CaseI
def caseICoeff (a b : ℤ) (k₁ k₂ : ℕ) : ℕ → ℤ := fun j ↦
  (if j = 0 then a else 0) + (if j = 1 then b else 0) -
    (if j = k₁ then a else 0) - (if j = k₂ then b else 0)
local notation "K" => CyclotomicField p ℚ
local notation "R" => 𝓞 K
variable [hpri : Fact p.Prime]
end FltRegular


