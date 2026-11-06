-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Coordinates
-- name    : OAI_NumberTheory_DirichletL_Hecke_Coordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T22:13:36.324518+00:00
-- url     : https://prove2.me/theorems/d5251983-35f9-4ecf-bd03-c93d9b78f6e7
-- title:
--   Coordinates
-- statement:
--   Definitions and structural lemmas for Coordinates, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/Coordinates.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Family
import Mathlib.Data.ZMod.Basic
import Theorems.Thm_OAI_SevenEighths_EisensteinTheta_parityPair_k
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_elementCoeff_one
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_quotient_period
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_pair_k
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_k
attribute [local simp] OAI.SevenEighths.EisensteinTheta.parityPair_k
attribute [local simp] OAI.SevenEighths.HeckeFamily.elementCoeff_one
attribute [local simp] OAI.SevenEighths.HeckeTheta.pair_k
attribute [local simp] OAI.SevenEighths.ThetaProduct.rectangularPair_k


set_option autoImplicit false
namespace OAI
noncomputable section
namespace SevenEighths.HeckeCoordinates
open HeckeFamily
instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
theorem hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta 3 ℚ K) 3 := IsCyclotomicExtension.zeta_spec 3 ℚ K
def pb : PowerBasis ℤ O := hζ.integralPowerBasis
def intQuotientHom (χ : Character) : ℤ →+ (O ⧸ χ.modulus) :=
  (Ideal.Quotient.mk χ.modulus).toAddMonoidHom.comp (Int.castAddHom O)
def zmodQuotientHom (χ : Character) : ZMod χ.period →+ (O ⧸ χ.modulus) :=
  ZMod.lift χ.period ⟨intQuotientHom χ, by
    change Ideal.Quotient.mk χ.modulus ((χ.period : ℤ) : O) = 0
    simpa only [Int.cast_natCast] using quotient_period χ⟩
@[simp] theorem zmodQuotientHom_intCast (χ : Character) (a : ℤ) :
    zmodQuotientHom χ (a : ZMod χ.period) = Ideal.Quotient.mk χ.modulus (a : O) :=
  ZMod.lift_coe _ _ _
@[simp] theorem zmodQuotientHom_natCast (χ : Character) (a : ℕ) :
    zmodQuotientHom χ (a : ZMod χ.period) = Ideal.Quotient.mk χ.modulus (a : O) := by
  simpa only [Int.cast_natCast] using zmodQuotientHom_intCast χ (a : ℤ)
def coordinateQuotientHom (χ : Character) :
    (ZMod χ.period × ZMod χ.period) →+ (O ⧸ χ.modulus) where
  toFun p := zmodQuotientHom χ p.1 +
    zmodQuotientHom χ p.2 * Ideal.Quotient.mk χ.modulus HeckeFamily.omega
  map_zero' := by simp
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring
end SevenEighths.HeckeCoordinates
end
end OAI


