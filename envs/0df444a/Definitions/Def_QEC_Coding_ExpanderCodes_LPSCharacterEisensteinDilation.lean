-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
-- name    : QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T03:02:04.095282+00:00
-- url     : https://prove2.me/theorems/470e6624-bb02-4350-b7e5-9595becd6527
-- title:
--   LPSCharacter Eisenstein Dilation
-- statement:
--   Definitions and structural lemmas for LPSCharacter Eisenstein Dilation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSL2Z_firstColumn_gcd_one

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
lemma lpsEisensteinDilation_column_gcd (m : ℕ) (γ : SL(2,ℤ)) :
    Int.gcd ((m:ℤ)*γ 0 0) (γ 1 0)=Int.gcd (m:ℤ) (γ 1 0) := by
  exact Int.gcd_mul_left_left_of_gcd_eq_one (lpsSL2Z_firstColumn_gcd_one γ)
lemma lpsEisensteinDilation_column_gcd_pos (m : ℕ) (hm : 0<m) (γ : SL(2,ℤ)) :
    0<Int.gcd ((m:ℤ)*γ 0 0) (γ 1 0) := by
  rw [lpsEisensteinDilation_column_gcd]
  exact Int.gcd_pos_iff.mpr (Or.inl (by exact_mod_cast hm.ne'))
def lpsEisensteinDilationCuspMatrix (m : ℕ) (hm : 0<m) (γ : SL(2,ℤ)) : SL(2,ℤ) :=
  lpsE2IntegerPrimitiveColumn
    (((m:ℤ)*γ 0 0)/(Int.gcd ((m:ℤ)*γ 0 0) (γ 1 0):ℤ))
    ((γ 1 0)/(Int.gcd ((m:ℤ)*γ 0 0) (γ 1 0):ℤ))
    (Int.gcd_div_gcd_div_gcd (lpsEisensteinDilation_column_gcd_pos m hm γ))
end QEC.Coding.TannerLiftedProduct


