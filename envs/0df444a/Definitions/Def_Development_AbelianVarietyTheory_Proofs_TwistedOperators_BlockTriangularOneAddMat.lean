-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:17.881915+00:00
-- url     : https://prove2.me/theorems/438d60a7-0b2b-4f9a-b8a8-e0b172973fc4
-- title:
--   Block Triangular One Add Mat
-- statement:
--   Definitions and structural lemmas for Block Triangular One Add Mat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_leviEmb_mem_normalizer
import Theorems.Thm_GlobalTheory_SmGL_mem_unipRad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped Kronecker
namespace GlobalTheory.SmGL.UnipHaar
section Algebra
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
abbrev Idx (e : (Σ a, m a) ≃ n) : Type := {p : n × n // blk e p.1 < blk e p.2}
variable (e : (Σ a, m a) ≃ n)
def ent (X : Matrix n n R) : Idx e → R := fun p => X p.1.1 p.1.2
def mat (x : Idx e → R) : Matrix n n R :=
  Matrix.of fun i j => if h : blk e i < blk e j then x ⟨(i, j), h⟩ else 0
def lmat (A : Matrix n n R) : Matrix (Idx e) (Idx e) R :=
  Matrix.of fun p q => if p.1.2 = q.1.2 then A p.1.1 q.1.1 else 0
def rmat (B : Matrix n n R) : Matrix (Idx e) (Idx e) R :=
  Matrix.of fun p q => if p.1.1 = q.1.1 then B q.1.2 p.1.2 else 0
omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
theorem ent_mat (x : Idx e → R) : ent e (mat e x) = x := by
  funext p
  simp [ent, mat, p.2]
omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] in
theorem ent_one_add (X : Matrix n n R) : ent e (1 + X) = ent e X := by
  funext p
  have : p.1.1 ≠ p.1.2 := fun h => p.2.ne (by rw [h])
  simp [ent, this]
theorem eq_one_add_mat {u : GL n R} (hu : u ∈ unipRad R e) :
    (u : Matrix n n R) = 1 + mat e (ent e (u : Matrix n n R)) := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 hu
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  rcases lt_trichotomy a b with h | rfl | h
  · simp [mat, ent, h, one_apply, h.ne]
  · simp [mat, h2, one_apply]
  · simp [mat, h.not_gt, one_apply, h.ne', mem_parab_iff.1 h1 a b i j h]
omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] in
theorem blockTriangular_one_add_mat (x : Idx e → R) : (1 + mat e x).BlockTriangular (blk e) :=
  blockTriangular_one.add fun i j h => by simp [mat, h.not_gt]
omit [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in
theorem det_one_add_mat (x : Idx e → R) : (1 + mat e x).det = 1 := by
  rw [(blockTriangular_one_add_mat e x).det_fintype]
  refine Finset.prod_eq_one fun a _ => ?_
  have : (1 + mat e x).toSquareBlock (blk e) a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp [toSquareBlock_def, mat, hi, hj, one_apply]
  rw [this, det_one]
def unipEquiv : unipRad R e ≃ (Idx e → R) where
  toFun u := ent e ((u : GL n R) : Matrix n n R)
  invFun x := ⟨GeneralLinearGroup.mk'' (1 + mat e x) (by rw [det_one_add_mat]; exact isUnit_one),
    mem_unipRad.2 ⟨blockTriangular_one_add_mat e x, fun a i j => by
      show (1 + mat e x) _ _ = _
      simp [mat, one_apply]⟩⟩
  left_inv u := Subtype.ext (Units.ext (eq_one_add_mat e u.2).symm)
  right_inv x := (ent_one_add e _).trans (ent_mat e x)
def rowEquiv (a : α) : m a × {j : n // a < blk e j} ≃ {p : Idx e // blk e p.1.1 = a} :=
  Equiv.ofBijective (fun x => ⟨⟨(e ⟨a, x.1⟩, x.2.1), by simpa using x.2.2⟩, by simp⟩) ⟨by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simpa [Subtype.ext_iff] using h, by
    rintro ⟨⟨⟨i, j⟩, h⟩, hi⟩
    obtain ⟨⟨b, i⟩, rfl⟩ := e.surjective i
    obtain rfl : b = a := by simpa using hi
    exact ⟨(i, ⟨j, by simpa using h⟩), rfl⟩⟩
def colEquiv (a : α) : m a × {j : n // blk e j < a} ≃ {p : Idx e // blk e p.1.2 = a} :=
  Equiv.ofBijective (fun x => ⟨⟨(x.2.1, e ⟨a, x.1⟩), by simpa using x.2.2⟩, by simp⟩) ⟨by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simpa [Subtype.ext_iff, and_comm] using h, by
    rintro ⟨⟨⟨i, j⟩, h⟩, hi⟩
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    obtain rfl : b = a := by simpa using hi
    exact ⟨(j, ⟨i, by simpa using h⟩), rfl⟩⟩
def conj (g : Levi R m) (u : unipRad R e) : unipRad R e :=
  ⟨leviEmb R e g * u * (leviEmb R e g)⁻¹,
    (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer R e g) _).1 u.2⟩
def cmat (g : Levi R m) : Matrix (Idx e) (Idx e) R :=
  rmat e (leviEmb R e g⁻¹ : Matrix n n R) * lmat e (leviEmb R e g : Matrix n n R)
variable [TopologicalSpace R] [IsTopologicalRing R]
def unipHomeo : unipRad R e ≃ₜ (Idx e → R) where
  toEquiv := unipEquiv e
  continuous_toFun := continuous_pi fun p =>
    (Units.continuous_val.comp continuous_subtype_val).matrix_elem p.1.1 p.1.2
  continuous_invFun := by
    have h : Continuous fun x : Idx e → R => 1 + mat e x := by
      refine continuous_const.add (continuous_matrix fun i j => ?_)
      by_cases h : blk e i < blk e j
      · simp only [mat, of_apply, h, dif_pos]
        exact continuous_apply _
      · simp only [mat, of_apply, h, dif_neg, not_false_eq_true]
        exact continuous_const
    refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨h, h.matrix_adjugate.congr fun x => ?_⟩) _
    rw [Matrix.coe_units_inv, Matrix.inv_def]
    show _ = Ring.inverse (1 + mat e x).det • (1 + mat e x).adjugate
    rw [det_one_add_mat, Ring.inverse_one, one_smul]
end Algebra
section Measure
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
  [MeasurableSpace (unipRad k e)] [BorelSpace (unipRad k e)] [MeasurableSpace k] [BorelSpace k]
  (ν : Measure k) [ν.IsAddHaarMeasure]
end Measure
end GlobalTheory.SmGL.UnipHaar


