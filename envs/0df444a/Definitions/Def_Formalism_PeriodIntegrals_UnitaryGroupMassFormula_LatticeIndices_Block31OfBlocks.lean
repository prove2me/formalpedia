-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_Block31OfBlocks
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_Block31OfBlocks
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:58.624992+00:00
-- url     : https://prove2.me/theorems/755a2ce0-b961-455a-891f-3ab94d3cc3a9
-- title:
--   Block31 Of Blocks
-- statement:
--   Definitions and structural lemmas for Block31 Of Blocks, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/Block31OfBlocks.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_LeviEmbeddingBlock32
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
namespace MassDataIdxStIm
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3
section Count
variable {A : Type} [CommRing A]
def uniEquiv (n : ℕ) : {u : Matrix (Fin n) (Fin n) A // IsUpUni u} ≃ ({p : Fin n × Fin n // p.1 < p.2} → A) where
  toFun u := fun p => u.1 p.1.1 p.1.2
  invFun f := ⟨Matrix.of fun i j => if h : i < j then f ⟨(i, j), h⟩ else if i = j then 1 else 0, by
    constructor
    · intro i j hij
      have hij' : j < i := hij
      simp [not_lt.2 hij'.le, hij'.ne']
    · intro a; simp⟩
  left_inv u := by
    apply Subtype.ext
    ext i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h]
    · subst h; simp [u.2.2 i]
    · have : u.1 i j = 0 := u.2.1 h
      simp [not_lt.2 h.le, h.ne', this]
  right_inv f := by
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    have h' : i < j := h
    simp [h']
noncomputable def upUniGEquiv (n : ℕ) : upUniG A n ≃ {u : Matrix (Fin n) (Fin n) A // IsUpUni u} where
  toFun g := ⟨g.1.1, g.2⟩
  invFun u := ⟨Matrix.GeneralLinearGroup.mk'' u.1 (uni_unit u.2), u.2⟩
  left_inv g := Subtype.ext (Units.ext rfl)
  right_inv u := rfl
noncomputable def glEquiv (n : ℕ) : GL (Fin n) A ≃ {h : Matrix (Fin n) (Fin n) A // IsUnit h.det} where
  toFun g := ⟨g.1, (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit⟩
  invFun h := Matrix.GeneralLinearGroup.mk'' h.1 h.2
  left_inv g := Units.ext rfl
  right_inv h := rfl
variable {r k : ℕ}
def mk (a : Matrix (Fin r) (Fin r) A) (b : Matrix (Fin r) (Mid k) A) (c : Matrix (Fin r) (Fin r) A)
    (m : Matrix (Mid k) (Mid k) A) (e : Matrix (Mid k) (Fin r) A) (f : Matrix (Fin r) (Fin r) A) :
    Matrix (Idx r k) (Idx r k) A :=
  Matrix.fromBlocks a (Matrix.fromCols b c) 0 (Matrix.fromBlocks m e 0 f)
section mk
variable (a : Matrix (Fin r) (Fin r) A) (b : Matrix (Fin r) (Mid k) A) (c : Matrix (Fin r) (Fin r) A)
    (m : Matrix (Mid k) (Mid k) A) (e : Matrix (Mid k) (Fin r) A) (f : Matrix (Fin r) (Fin r) A)
theorem block11_of_blocks : b11 (mk a b c m e f) = a := by
  first
    | rfl
    | (ext i j; simp [mk, b11])
theorem block21_of_blocks : b21 (mk a b c m e f) = 0 := by
  first
    | rfl
    | (ext i j; simp [mk, b21])
theorem block22_of_blocks : b22 (mk a b c m e f) = m := by
  first
    | rfl
    | (ext i j; simp [mk, b22])
theorem block31_of_blocks : b31 (mk a b c m e f) = 0 := by
  first
    | rfl
    | (ext i j; simp [mk, b31])
theorem block32_of_blocks : b32 (mk a b c m e f) = 0 := by
  first
    | rfl
    | (ext i j; simp [mk, b32])
theorem block33_of_blocks : b33 (mk a b c m e f) = f := by
  first
    | rfl
    | (ext i j; simp [mk, b33])
end mk
def parMap (P : Matrix (Fin k) (Fin k) A → Prop) :
    ({a : Matrix (Fin r) (Fin r) A // IsUpUni a} × {f : Matrix (Fin r) (Fin r) A // IsUpUni f} ×
      {h : Matrix (Fin k) (Fin k) A // P h} × Matrix (Fin r) (Mid k) A × Matrix (Fin r) (Fin r) A ×
      Matrix (Mid k) (Fin r) A) → {x : Matrix (Idx r k) (Idx r k) A // Par P x} :=
  fun t => ⟨mk t.1.1 t.2.2.2.1 t.2.2.2.2.1 (midEmb t.2.2.1.1) t.2.2.2.2.2 t.2.1.1,
    by rw [block11_of_blocks]; exact t.1.2, by rw [block33_of_blocks]; exact t.2.1.2, block21_of_blocks .., block31_of_blocks .., block32_of_blocks ..,
    t.2.2.1.1, t.2.2.1.2, block22_of_blocks ..⟩
end Count
end MassDataIdxStIm


