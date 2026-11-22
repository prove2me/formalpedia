-- Prove2me | Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
-- name    : ReciprocityTheory_GaloisValuations_GlobalB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:47:49.090535+00:00
-- url     : https://prove2.me/theorems/c1b2ca83-c26e-4e96-bbf6-f9418517b3ff
-- title:
--   Global B
-- statement:
--   Definitions and structural lemmas for Global B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalB.lean

import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open scoped nonZeroDivisors
namespace ReciprocityTheory.Gal
section den
variable {Ω : Type*} [Field Ω]
theorem isIntegral_int_of_isIntegral {F : Type*} [Field F] [NumberField F] [Algebra F Ω] {b : Ω} (hb : IsIntegral (𝓞 F) b) : IsIntegral ℤ b :=
  isIntegral_trans b hb
theorem mem_of_isIntegral_int (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) : b ∈ A := by
  have h1 : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1
  rw [← hy]
  exact y.2
end den
section places
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
variable (F Ω) in

abbrev IntCl := integralClosure (𝓞 F) Ω
theorem valuation_le_one_intCl (A : ValuationSubring Ω) (b : IntCl F Ω) :
    A.valuation (b : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (isIntegral_int_of_isIntegral b.2))
def primeBelow (A : ValuationSubring Ω) : Ideal (IntCl F Ω) where
  carrier := {b | A.valuation (b : Ω) < 1}
  add_mem' {a b} ha hb := by
    show A.valuation ((a : Ω) + b) < 1
    exact Valuation.map_add_lt _ ha hb
  zero_mem' := by show A.valuation ((0 : IntCl F Ω) : Ω) < 1; simp
  smul_mem' c b hb := by
    show A.valuation ((c : Ω) * b) < 1
    rw [Valuation.map_mul]
    calc A.valuation (c : Ω) * A.valuation (b : Ω) ≤ 1 * A.valuation (b : Ω) :=
          mul_le_mul_left (valuation_le_one_intCl A c) _
      _ < 1 := by rw [one_mul]; exact hb
theorem mem_primeBelow {A : ValuationSubring Ω} {b : IntCl F Ω} :
    b ∈ primeBelow A ↔ A.valuation (b : Ω) < 1 := Iff.rfl
instance isPrime_primeBelow (A : ValuationSubring Ω) : (primeBelow (F := F) A).IsPrime where
  ne_top' h := by
    have : (1 : IntCl F Ω) ∈ primeBelow A := h ▸ Submodule.mem_top
    rw [mem_primeBelow] at this
    simp at this
  mem_or_mem' {a b} hab := by
    rw [mem_primeBelow, mem_primeBelow]
    rw [mem_primeBelow] at hab
    by_contra hn
    simp only [not_or, not_lt] at hn
    have ha : A.valuation (a : Ω) = 1 := le_antisymm (valuation_le_one_intCl A a) hn.1
    have hb : A.valuation (b : Ω) = 1 := le_antisymm (valuation_le_one_intCl A b) hn.2
    have : A.valuation ((a * b : IntCl F Ω) : Ω) = 1 := by
      rw [MulMemClass.coe_mul, Valuation.map_mul, ha, hb, one_mul]
    rw [this] at hab
    exact lt_irrefl _ hab
end places
section profinite
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
end profinite
end ReciprocityTheory.Gal


