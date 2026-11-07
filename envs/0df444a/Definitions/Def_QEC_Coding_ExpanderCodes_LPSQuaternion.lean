-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
-- name    : QEC_Coding_ExpanderCodes_LPSQuaternion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T21:32:17.588248+00:00
-- url     : https://prove2.me/theorems/0d623a22-ef50-4a7f-be78-e12d43b627ff
-- title:
--   LPSQuaternion
-- statement:
--   Definitions and structural lemmas for LPSQuaternion, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternion.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResiduePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResidueCoordinates
import Mathlib.FieldTheory.Finite.Basic
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_projectiveDetIsSquare_iff_mem_range_toPGL
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_projectiveDetIsSquare_mk_of_det
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSResiduePrime_degree_nonzero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveResidueX_sq_add_lpsEffectiveResidueY_sq_add_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
open Matrix
open QEC.Coding.BalancedProduct.LPSArithmetic
variable {p : ℕ}
structure LPSQuaternion where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq
@[ext] theorem LPSQuaternion.ext {t u : LPSQuaternion}
    (ha : t.a = u.a) (hb : t.b = u.b)
    (hc : t.c = u.c) (hd : t.d = u.d) : t = u := by
  cases t
  cases u
  simp_all
def LPSQuaternion.norm (t : LPSQuaternion) : ℤ :=
  t.a ^ 2 + t.b ^ 2 + t.c ^ 2 + t.d ^ 2
def LPSQuaternion.conj (t : LPSQuaternion) : LPSQuaternion where
  a := t.a
  b := -t.b
  c := -t.c
  d := -t.d
@[simp] theorem LPSQuaternion.conj_a (t : LPSQuaternion) :
    t.conj.a = t.a := rfl
@[simp] theorem LPSQuaternion.conj_b (t : LPSQuaternion) :
    t.conj.b = -t.b := rfl
@[simp] theorem LPSQuaternion.conj_c (t : LPSQuaternion) :
    t.conj.c = -t.c := rfl
@[simp] theorem LPSQuaternion.conj_d (t : LPSQuaternion) :
    t.conj.d = -t.d := rfl
@[simp] theorem LPSQuaternion.conj_conj (t : LPSQuaternion) :
    t.conj.conj = t := by
  cases t
  simp [LPSQuaternion.conj]
@[simp] theorem LPSQuaternion.norm_conj (t : LPSQuaternion) :
    t.conj.norm = t.norm := by
  simp [LPSQuaternion.norm]
def lpsResidueX (q : ℕ) [Fact q.Prime] : ZMod q :=
  lpsEffectiveResidueX q
def lpsResidueY (q : ℕ) [Fact q.Prime] : ZMod q :=
  lpsEffectiveResidueY q
theorem lpsResidueX_sq_add_lpsResidueY_sq_add_one
    (q : ℕ) [Fact q.Prime] :
    lpsResidueX q ^ 2 + lpsResidueY q ^ 2 + 1 = 0 :=
  lpsEffectiveResidueX_sq_add_lpsEffectiveResidueY_sq_add_one q
def lpsQuaternionMatrix
    (q : ℕ) [Fact q.Prime]
    (t : LPSQuaternion) : Matrix (Fin 2) (Fin 2) (ZMod q) :=
  let a : ZMod q := t.a
  let b : ZMod q := t.b
  let c : ZMod q := t.c
  let d : ZMod q := t.d
  let x := lpsResidueX q
  let y := lpsResidueY q
  !![a + b * x + d * y, -b * y + c + d * x;
     -b * y - c + d * x, a - b * x - d * y]
theorem det_lpsQuaternionMatrix
    (q : ℕ) [Fact q.Prime] (t : LPSQuaternion) :
    (lpsQuaternionMatrix q t).det = (t.norm : ZMod q) := by
  have hroot := lpsResidueX_sq_add_lpsResidueY_sq_add_one q
  simp only [lpsQuaternionMatrix, LPSQuaternion.norm,
    Matrix.det_fin_two_of]
  push_cast
  linear_combination
    -((t.b : ZMod q) ^ 2 + (t.d : ZMod q) ^ 2) * hroot
noncomputable def lpsQuaternionGL
    (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    GL (Fin 2) (ZMod a.q) :=
  Matrix.GeneralLinearGroup.mk'' (lpsQuaternionMatrix a.q t) <| by
    rw [det_lpsQuaternionMatrix, ht]
    apply isUnit_iff_ne_zero.mpr
    simpa using a.degree_nonzero
theorem lpsQuaternionGL_det
    (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    ((lpsQuaternionGL a t ht).det : ZMod a.q) = (p : ZMod a.q) := by
  change (lpsQuaternionMatrix a.q t).det = (p : ZMod a.q)
  rw [det_lpsQuaternionMatrix, ht]
  norm_cast
noncomputable def lpsQuaternionPGL
    (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) : PGL(2, ZMod a.q) :=
  Matrix.ProjGenLinGroup.mk (lpsQuaternionGL a t ht)
theorem projectiveDetIsSquare_lpsQuaternionPGL
    (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    ProjectiveDetIsSquare (lpsQuaternionPGL a t ht) := by
  exact projectiveDetIsSquare_mk_of_det
    (lpsQuaternionGL a t ht) (lpsQuaternionGL_det a t ht)
      a.degree_nonzero a.residue
theorem lpsQuaternionPGL_mem_range_toPGL
    (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    lpsQuaternionPGL a t ht ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := ZMod a.q)).range := by
  exact (projectiveDetIsSquare_iff_mem_range_toPGL _).mp
    (projectiveDetIsSquare_lpsQuaternionPGL a t ht)
noncomputable def lpsQuaternionPSL
    (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) : PSL(2, ZMod a.q) :=
  Classical.choose (lpsQuaternionPGL_mem_range_toPGL a t ht)
end QEC.Coding.TannerLiftedProduct


