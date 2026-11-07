-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
-- name    : QEC_Coding_ExpanderCodes_QuadraticTorusIndex
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T11:33:18.586464+00:00
-- url     : https://prove2.me/theorems/3f5b3cf9-6c28-4ef7-b0ff-1567cc97a59d
-- title:
--   Quadratic Torus Index
-- statement:
--   Definitions and structural lemmas for Quadratic Torus Index, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticTorusIndex.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_alphaUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_baseUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_primeUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_baseUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_primeUnit


set_option autoImplicit false
noncomputable section
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]
def scalarKernel (epsilon : F) : Subgroup (QuadraticAlgebra F epsilon 0)ˣ :=
  (constantProjectiveMap (RingHom.id F) epsilon 0).ker
abbrev TorusIndex (epsilon : F) :=
  (QuadraticAlgebra F epsilon 0)ˣ ⧸ scalarKernel epsilon
theorem scalarKernel_eq (f : F →+* K) (epsilon : F) (y : K)
    (hTwoF : (2 : F) ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    scalarKernel epsilon = (constantProjectiveMap f epsilon y).ker := by
  ext a
  change constantProjectiveMap (RingHom.id F) epsilon 0 a = 1 ↔
    constantProjectiveMap f epsilon y a = 1
  rw [constantProjectiveMap_eq_one_iff (RingHom.id F) epsilon 0 (by simp) hTwoF,
    constantProjectiveMap_eq_one_iff f epsilon y hOne hTwo]
def torusIndexEquiv (f : F →+* K) (epsilon : F) (y : K)
    (hTwoF : (2 : F) ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    TorusIndex epsilon ≃* constantTorus f epsilon y :=
  (QuotientGroup.quotientMulEquivOfEq
    (scalarKernel_eq f epsilon y hTwoF hOne hTwo)).trans
      (QuotientGroup.quotientKerEquivRange (constantProjectiveMap f epsilon y))
def torusIndexMap (f : F →+* K) (epsilon : F) (y : K)
    (hTwoF : (2 : F) ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    TorusIndex epsilon →* ProjectiveGroup (f epsilon) y :=
  (constantTorus f epsilon y).subtype.comp
    (torusIndexEquiv f epsilon y hTwoF hOne hTwo).toMonoidHom
instance finiteTorusIndex (epsilon : F) [Finite F] : Finite (TorusIndex epsilon) := by
  letI : Finite (QuadraticAlgebra F epsilon 0) :=
    Finite.of_equiv (F × F) (QuadraticAlgebra.equivProd epsilon 0).symm
  infer_instance
instance fintypeTorusIndex (epsilon : F) [Fintype F] : Fintype (TorusIndex epsilon) :=
  Fintype.ofFinite _
def torusIndexAlpha (epsilon : F) (hEpsilon : epsilon ≠ 0) : TorusIndex epsilon :=
  QuotientGroup.mk (quadraticAlphaUnit epsilon hEpsilon)
def indexedLeft (f : F →+* K) (epsilon : F) (y : K)
    (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) (t : TorusIndex epsilon) : ProjectiveGroup (f epsilon) y :=
  torusIndexMap f epsilon y hTwoF hOne hTwo t * projectiveBase (f epsilon) y hY hOne *
    (torusIndexMap f epsilon y hTwoF hOne hTwo t)⁻¹
def indexedRight (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) (t : TorusIndex epsilon) :
    ProjectiveGroup (f epsilon) y :=
  torusIndexMap f epsilon y hTwoF hOne hTwo t *
      projectivePrime (f epsilon) y ((map_ne_zero f).mpr hEpsilon) hY hOne *
    (torusIndexMap f epsilon y hTwoF hOne hTwo t)⁻¹
def indexedLeftInverse (epsilon : F) (hEpsilon : epsilon ≠ 0) :
    Equiv.Perm (TorusIndex epsilon) := Equiv.mulRight (torusIndexAlpha epsilon hEpsilon)
end QEC.Coding.ExpanderCodes.QuaternionGenerators


