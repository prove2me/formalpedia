-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionReduction
-- name    : QEC_Coding_ExpanderCodes_LPSQuaternionReduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:35:28.309245+00:00
-- url     : https://prove2.me/theorems/a0098239-ced1-417b-a3fc-745eda7956ad
-- title:
--   LPSQuaternion Reduction
-- statement:
--   Definitions and structural lemmas for LPSQuaternion Reduction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionReduction.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionRing
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSResiduePrime_degree_nonzero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
noncomputable def lpsQuaternionAwaySubmonoid
    (q : ℕ) [Fact q.Prime] : Submonoid LPSQuaternion where
  carrier := {t | IsUnit (t.norm : ZMod q)}
  one_mem' := by simp
  mul_mem' {t u} ht hu := by
    simpa using ht.mul hu
@[simp] theorem mem_lpsQuaternionAwaySubmonoid_iff
    (q : ℕ) [Fact q.Prime] (t : LPSQuaternion) :
    t ∈ lpsQuaternionAwaySubmonoid q ↔
      IsUnit (t.norm : ZMod q) :=
  Iff.rfl
noncomputable def lpsQuaternionAwayGL
    (q : ℕ) [Fact q.Prime] :
    lpsQuaternionAwaySubmonoid q →* GL (Fin 2) (ZMod q) where
  toFun t := Matrix.GeneralLinearGroup.mk''
    (lpsQuaternionMatrix q t.1) <| by
      rw [det_lpsQuaternionMatrix]
      exact t.2
  map_one' := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact congrFun (congrFun (map_one (lpsQuaternionMatrixRingHom q)) i) j
  map_mul' t u := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact congrFun
      (congrFun (map_mul (lpsQuaternionMatrixRingHom q) t.1 u.1) i) j
@[simp] theorem coe_lpsQuaternionAwayGL
    (q : ℕ) [Fact q.Prime]
    (t : lpsQuaternionAwaySubmonoid q) :
    (lpsQuaternionAwayGL q t : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      lpsQuaternionMatrix q t.1 :=
  rfl
noncomputable def lpsQuaternionAwayPGL
    (q : ℕ) [Fact q.Prime] :
    lpsQuaternionAwaySubmonoid q →* PGL(2, ZMod q) :=
  Matrix.ProjGenLinGroup.mk.comp (lpsQuaternionAwayGL q)
@[simp] theorem lpsQuaternionAwayPGL_apply
    (q : ℕ) [Fact q.Prime]
    (t : lpsQuaternionAwaySubmonoid q) :
    lpsQuaternionAwayPGL q t =
      Matrix.ProjGenLinGroup.mk (lpsQuaternionAwayGL q t) :=
  rfl
noncomputable def lpsQuaternionAwayElement
    (a : LPSResiduePrime p) (t : LPSQuaternion) (ht : t.norm = p) :
    lpsQuaternionAwaySubmonoid a.q :=
  ⟨t, by
    apply isUnit_iff_ne_zero.mpr
    rw [ht]
    simpa only [Int.cast_natCast] using a.degree_nonzero⟩
end QEC.Coding.TannerLiftedProduct


