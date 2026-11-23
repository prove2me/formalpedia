-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:47:01.327962+00:00
-- url     : https://prove2.me/theorems/621498c1-2559-4881-b3f8-8f09799ea927
-- title:
--   Simple Sum Row Col
-- statement:
--   Definitions and structural lemmas for Simple Sum Row Col, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SimpleSumRowCol.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
namespace GlobalTheory.RootEx.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
theorem inN_tri {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : InN p g) : g.val.BlockTriangular (lev p) := by
  intro r s h
  rw [hg r s h.le, Matrix.one_apply_ne]
  rintro rfl; exact lt_irrefl _ h
theorem mul_entry {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : InN p g) {h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k}
    (hh : h.BlockTriangular (lev p)) (r s) (hrs : lev p s ≤ lev p r) : (g.val * h) r s = h r s := by
  have : (g.val * h) r s = ((1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * h) r s := by
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : lev p t ≤ lev p r
    · rw [hg r t ht]
    · rw [hh (show lev p s < lev p t by omega)]; simp
  rw [this, Matrix.one_mul]
def Nsub (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c p : ℕ) : Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | InN p g}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun {a b} ha hb r s hrs => by
    rw [Units.val_mul, mul_entry ha (inN_tri hb) r s hrs, hb r s hrs]
  inv_mem' := fun {a} ha r s hrs => by
    have h1 : (a⁻¹).val.BlockTriangular (lev p) := by
      rw [Matrix.coe_units_inv]
      haveI := a.invertible
      exact Matrix.blockTriangular_inv_of_blockTriangular (inN_tri ha)
    rw [← mul_entry ha h1 r s hrs, Units.mul_inv]
theorem mem_N_iff {p : ℕ} {g : GL (n ⊕ Fin c) k} : g ∈ N k n c p ↔ InN p g := by
  have : N k n c p = Nsub k n c p := Subgroup.closure_eq (Nsub k n c p)
  rw [this]; rfl
def mkN (p : ℕ) (e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2} → k) :
    Matrix (n ⊕ Fin c) (n ⊕ Fin c) k :=
  Matrix.of fun r s => if h : lev p r < lev p s then e ⟨(r, s), h⟩ else (1 : Matrix _ _ k) r s
theorem det_mkN (p : ℕ) (e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2} → k) :
    (mkN p e).det = 1 := by
  have ht : (mkN p e).BlockTriangular (lev p) := by
    intro r s h
    have : r ≠ s := by rintro rfl; exact lt_irrefl _ h
    simp [mkN, not_lt.2 h.le, this]
  rw [ht.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : (mkN p e).toSquareBlock (lev p) a = 1 := by
    ext ⟨r, hr⟩ ⟨s, hs⟩
    simp [toSquareBlock_def, mkN, hr, hs, Matrix.one_apply]
  rw [this, det_one]
def mkNel (p : ℕ) (e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2} → k) : N k n c p :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (mkN p e) (by rw [det_mkN]; exact one_ne_zero), by
    rw [mem_N_iff]
    intro r s h
    show mkN p e r s = _
    simp [mkN, not_lt.2 h]⟩
section meas
variable [MeasurableSpace k]
end meas
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open Classical in

def chi (ψ : AddChar k Circle) (p : ℕ) (h : GL (n ⊕ Fin c) k) : ℂ :=
  if h ∈ N k n c p then (ψ (simpleSum h) : ℂ) else 0
def reg (G : Type*) [Group G] : Representation ℂ G (G →₀ ℂ) where
  toFun g := Finsupp.lmapDomain ℂ ℂ (g * ·)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_assoc]
end GlobalTheory.RootEx.Model


