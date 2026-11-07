-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionShell
-- name    : QEC_Coding_ExpanderCodes_LPSQuaternionShell
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T21:32:58.428762+00:00
-- url     : https://prove2.me/theorems/b381b049-6cf4-4d52-a6de-bad3157ac018
-- title:
--   LPSQuaternion Shell
-- statement:
--   Definitions and structural lemmas for LPSQuaternion Shell, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionShell.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Mathlib.Data.Finset.Interval
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
def lpsQuaternionEquivTuple :
    LPSQuaternion ≃ (((ℤ × ℤ) × ℤ) × ℤ) where
  toFun t := (((t.a, t.b), t.c), t.d)
  invFun x := ⟨x.1.1.1, x.1.1.2, x.1.2, x.2⟩
  left_inv t := by cases t; rfl
  right_inv x := by rcases x with ⟨⟨⟨a, b⟩, c⟩, d⟩; rfl
noncomputable def lpsQuaternionCoordinateRange (p : ℕ) : Finset ℤ :=
  Finset.Icc (-(p : ℤ)) (p : ℤ)
noncomputable def lpsQuaternionBox (p : ℕ) : Finset LPSQuaternion :=
  let r := lpsQuaternionCoordinateRange p
  (((r.product r).product r).product r).map
    lpsQuaternionEquivTuple.symm.toEmbedding
theorem mem_lpsQuaternionBox_iff (p : ℕ) (t : LPSQuaternion) :
    t ∈ lpsQuaternionBox p ↔
      -(p : ℤ) ≤ t.a ∧ t.a ≤ p ∧
      -(p : ℤ) ≤ t.b ∧ t.b ≤ p ∧
      -(p : ℤ) ≤ t.c ∧ t.c ≤ p ∧
      -(p : ℤ) ≤ t.d ∧ t.d ≤ p := by
  simp [lpsQuaternionBox, lpsQuaternionCoordinateRange,
    lpsQuaternionEquivTuple, and_assoc]
def LPSQuaternion.IsNormalizedAt (p : ℕ) (t : LPSQuaternion) : Prop :=
  t.norm = p ∧ 0 < t.a ∧ Odd t.a
noncomputable instance (p : ℕ) (t : LPSQuaternion) :
    Decidable (t.IsNormalizedAt p) :=
  Classical.propDecidable _
noncomputable def lpsQuaternionShell (p : ℕ) : Finset LPSQuaternion :=
  (lpsQuaternionBox p).filter (LPSQuaternion.IsNormalizedAt p)
theorem coordinate_bounds_of_norm
    {p : ℕ} (hp : 0 < p) (t : LPSQuaternion)
    (ht : t.norm = p) :
    -(p : ℤ) ≤ t.a ∧ t.a ≤ p ∧
      -(p : ℤ) ≤ t.b ∧ t.b ≤ p ∧
      -(p : ℤ) ≤ t.c ∧ t.c ≤ p ∧
      -(p : ℤ) ≤ t.d ∧ t.d ≤ p := by
  have hnorm :
      t.a ^ 2 + t.b ^ 2 + t.c ^ 2 + t.d ^ 2 = (p : ℤ) := ht
  have ha : t.a ^ 2 ≤ (p : ℤ) := by
    nlinarith [sq_nonneg t.b, sq_nonneg t.c, sq_nonneg t.d]
  have hb : t.b ^ 2 ≤ (p : ℤ) := by
    nlinarith [sq_nonneg t.a, sq_nonneg t.c, sq_nonneg t.d]
  have hc : t.c ^ 2 ≤ (p : ℤ) := by
    nlinarith [sq_nonneg t.a, sq_nonneg t.b, sq_nonneg t.d]
  have hd : t.d ^ 2 ≤ (p : ℤ) := by
    nlinarith [sq_nonneg t.a, sq_nonneg t.b, sq_nonneg t.c]
  have hpz : (1 : ℤ) ≤ p := by exact_mod_cast hp
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.a + p)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.a - p)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.b + p)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.b - p)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.c + p)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.c - p)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.d + p)]
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.d - p)]
theorem mem_lpsQuaternionShell_iff
    {p : ℕ} (hp : 0 < p) (t : LPSQuaternion) :
    t ∈ lpsQuaternionShell p ↔ t.IsNormalizedAt p := by
  rw [lpsQuaternionShell, Finset.mem_filter]
  exact and_iff_right_of_imp fun ht =>
    (mem_lpsQuaternionBox_iff p t).mpr
      (coordinate_bounds_of_norm hp t ht.1)
theorem norm_eq_of_mem_lpsQuaternionShell
    {p : ℕ} (hp : 0 < p) {t : LPSQuaternion}
    (ht : t ∈ lpsQuaternionShell p) : t.norm = p :=
  ((mem_lpsQuaternionShell_iff hp t).mp ht).1
noncomputable def lpsQuaternionGeneratorsPSL
    (a : LPSResiduePrime p) : Finset PSL(2, ZMod a.q) := by
  classical
  exact (lpsQuaternionShell p).attach.image fun t =>
    lpsQuaternionPSL a t.1
      (norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos t.2)
end QEC.Coding.TannerLiftedProduct


