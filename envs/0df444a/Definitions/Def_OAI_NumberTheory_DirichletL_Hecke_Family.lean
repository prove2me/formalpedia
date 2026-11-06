-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Family
-- name    : OAI_NumberTheory_DirichletL_Hecke_Family
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:43:09.095871+00:00
-- url     : https://prove2.me/theorems/e80b414e-1c99-4ff1-bc59-393bc18d52a6
-- title:
--   Family
-- statement:
--   Definitions and structural lemmas for Family, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/Family.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Theorems.Thm_OAI_SevenEighths_EisensteinTheta_parityPair_k
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_pair_k
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_k
attribute [local simp] OAI.SevenEighths.EisensteinTheta.parityPair_k
attribute [local simp] OAI.SevenEighths.HeckeTheta.pair_k
attribute [local simp] OAI.SevenEighths.ThetaProduct.rectangularPair_k


set_option autoImplicit false
namespace OAI
noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeFamily
abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K
instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
def omega : O := (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger
def coordinateElement (x y : ℤ) : O := (x : O) + (y : O) * omega
structure Character where
  modulus : Ideal O
  modulus_ne_bot : modulus ≠ ⊥
  residue : MulChar (O ⧸ modulus) ℂ
  unit_trivial : ∀ u : Oˣ, residue (Ideal.Quotient.mk modulus (u : O)) = 1
  period : ℕ
  period_pos : 0 < period
  period_mem : (period : O) ∈ modulus
def Character.ofResidue (M : Ideal O) (hM : M ≠ ⊥)
    (χ : MulChar (O ⧸ M) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk M (u : O)) = 1) : Character := by
  letI : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient hM
  letI : Fintype (O ⧸ M) := Fintype.ofFinite _
  exact {
    modulus := M
    modulus_ne_bot := hM
    residue := χ
    unit_trivial := hu
    period := Fintype.card (O ⧸ M)
    period_pos := Fintype.card_pos
    period_mem := Ideal.Quotient.eq_zero_iff_mem.mp (by
      simpa only [map_natCast] using Nat.cast_card_eq_zero (O ⧸ M)) }
instance (χ : Character) : NeZero χ.period := ⟨Nat.ne_of_gt χ.period_pos⟩
def elementCoeff (χ : Character) (z : O) : ℂ := χ.residue (Ideal.Quotient.mk χ.modulus z)
def coefficients (χ : Character) (a : Fin χ.period × Fin χ.period) : ℂ :=
  elementCoeff χ (coordinateElement a.1 a.2)
def continuedLattice (χ : Character) : ℂ → ℂ := HeckeTheta.latticeL (coefficients χ)
end SevenEighths.HeckeFamily
end
end OAI


