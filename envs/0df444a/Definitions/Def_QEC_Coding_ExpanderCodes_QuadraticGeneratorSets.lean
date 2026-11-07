-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
-- name    : QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T11:32:36.459375+00:00
-- url     : https://prove2.me/theorems/77d12436-2353-475e-b5d0-698e2002a1bf
-- title:
--   Quadratic Generator Sets
-- statement:
--   Definitions and structural lemmas for Quadratic Generator Sets, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_alphaUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_baseUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_primeUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_baseUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_primeUnit


set_option autoImplicit false
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]
def quadraticAlphaUnit (epsilon : F) (hEpsilon : epsilon ≠ 0) :
    (QuadraticAlgebra F epsilon 0)ˣ where
  val := ⟨0, 1⟩
  inv := ⟨0, epsilon⁻¹⟩
  val_inv := by ext <;> simp [hEpsilon]
  inv_val := by ext <;> simp [hEpsilon]
def constantLeftSet (f : F →+* K) (epsilon : F) (y : K)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) : Set (ProjectiveGroup (f epsilon) y) :=
  conjugacySet (constantTorus f epsilon y) (projectiveBase (f epsilon) y hY hOne)
def constantRightSet (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    Set (ProjectiveGroup (f epsilon) y) :=
  conjugacySet (constantTorus f epsilon y)
    (projectivePrime (f epsilon) y ((map_ne_zero f).mpr hEpsilon) hY hOne)
end QEC.Coding.ExpanderCodes.QuaternionGenerators


