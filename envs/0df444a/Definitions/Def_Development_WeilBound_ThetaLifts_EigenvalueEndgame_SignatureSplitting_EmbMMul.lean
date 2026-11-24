-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_EmbMMul
-- name    : Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_EmbMMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:52.470207+00:00
-- url     : https://prove2.me/theorems/75bd7bd0-13bf-481e-9573-d0c21b415fef
-- title:
--   Emb MMul
-- statement:
--   Definitions and structural lemmas for Emb MMul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/EmbMMul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
namespace PositivityTheory.ThKEnd.Two
open Matrix GlobalTheory.WeilM
variable {S R d k : Type} [CommRing S] [CommRing R] [Algebra S R] [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
structure Dual (c : R →ₐ[S] R) (J : Matrix d d R) (X Y : Matrix d k R) : Prop where
  cc : ∀ a, c (c a) = a
  skew : (J.map c)ᵀ = -J
  xx : Xᵀ * J * X.map c = 0
  yy : Yᵀ * J * Y.map c = 0
  xy : Xᵀ * J * Y.map c = 1
def embM (c : R →ₐ[S] R) (J : Matrix d d R) (X Y : Matrix d k R) (g g' : Matrix k k R) : Matrix d d R :=
  1 + X * (g - 1) * (J * Y.map c)ᵀ - Y * (g' - 1) * (J * X.map c)ᵀ
variable {c : R →ₐ[S] R} {J : Matrix d d R} {X Y : Matrix d k R}
theorem mapc_mul {a b e : Type} [Fintype b] (A : Matrix a b R) (B : Matrix b e R) : (A * B).map c = A.map c * B.map c := by
  exact Matrix.map_mul (f := c.toRingHom)
theorem mapc_one {a : Type} [DecidableEq a] : (1 : Matrix a a R).map c = 1 := by
  exact Matrix.map_one _ (map_zero c) (map_one c)
theorem Dual.mcc (h : Dual c J X Y) {a b : Type} (A : Matrix a b R) : (A.map c).map c = A := by
  ext i j
  simp only [Matrix.map_apply]
  exact h.cc _
theorem mapc_transpose {a b : Type} (A : Matrix a b R) : (Aᵀ.map c) = (A.map c)ᵀ := by
  ext i j
  rfl
theorem mapc_add' {a b : Type} (A B : Matrix a b R) : (A + B).map c = A.map c + B.map c := by
  ext i j
  simp
theorem mapc_sub' {a b : Type} (A B : Matrix a b R) : (A - B).map c = A.map c - B.map c := by
  ext i j
  simp
theorem Dual.yx (h : Dual c J X Y) : Yᵀ * J * X.map c = -1 := by
  have e : ((Xᵀ * J * Y.map c).map c)ᵀ = (1 : Matrix k k R) := by
    rw [h.xy, mapc_one, transpose_one]
  rw [mapc_mul, mapc_mul, h.mcc, transpose_mul, transpose_mul, h.skew, mapc_transpose, transpose_transpose,
    Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc] at e
  exact neg_eq_iff_eq_neg.mp e
theorem tr_mul {e : Type} (Z : Matrix d k R) (T : Matrix d e R) : (J * Z.map c)ᵀ * T = (Tᵀ * J * Z.map c)ᵀ := by
  simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
theorem Dual.emb_mul (h : Dual c J X Y) (g g' f f' : Matrix k k R) :
    embM c J X Y g g' * embM c J X Y f f' = embM c J X Y (g * f) (g' * f') := by
  have hAX : ∀ {e : Type} (M : Matrix k e R), (J * Y.map c)ᵀ * (X * M) = M := by
    intro e M
    rw [← Matrix.mul_assoc, tr_mul, h.xy, transpose_one, Matrix.one_mul]
  have hAY : ∀ {e : Type} (M : Matrix k e R), (J * Y.map c)ᵀ * (Y * M) = 0 := by
    intro e M
    rw [← Matrix.mul_assoc, tr_mul, h.yy, transpose_zero, Matrix.zero_mul]
  have hBX : ∀ {e : Type} (M : Matrix k e R), (J * X.map c)ᵀ * (X * M) = 0 := by
    intro e M
    rw [← Matrix.mul_assoc, tr_mul, h.xx, transpose_zero, Matrix.zero_mul]
  have hBY : ∀ {e : Type} (M : Matrix k e R), (J * X.map c)ᵀ * (Y * M) = -M := by
    intro e M
    rw [← Matrix.mul_assoc, tr_mul, h.yx, transpose_neg, transpose_one, Matrix.neg_mul, Matrix.one_mul]
  have hAX1 : (J * Y.map c)ᵀ * X = 1 := by rw [tr_mul, h.xy, transpose_one]
  have hAY1 : (J * Y.map c)ᵀ * Y = 0 := by rw [tr_mul, h.yy, transpose_zero]
  have hBX1 : (J * X.map c)ᵀ * X = 0 := by rw [tr_mul, h.xx, transpose_zero]
  have hBY1 : (J * X.map c)ᵀ * Y = -1 := by rw [tr_mul, h.yx, transpose_neg, transpose_one]
  simp only [embM, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc, hAX, hAY, hBX, hBY, hAX1, hAY1, hBX1, hBY1, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg,
    Matrix.neg_mul, sub_zero, zero_sub, add_zero, zero_add, sub_neg_eq_add, neg_neg]
  abel
theorem Dual.emb_tr (h : Dual c J X Y) (g f : Matrix k k R) :
    (embM c J X Y g (f.map c)ᵀ)ᵀ * J = J * (embM c J X Y f (g.map c)ᵀ).map c := by
  simp only [embM, transpose_add, transpose_sub, transpose_one, transpose_mul, transpose_transpose, mapc_add',
    mapc_sub', mapc_mul, mapc_one, mapc_transpose, h.mcc, h.skew, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  abel
theorem star_mul (g f : GL k R) : ((((g * f)⁻¹).1).map c)ᵀ = ((g⁻¹).1.map c)ᵀ * ((f⁻¹).1.map c)ᵀ := by
  rw [_root_.mul_inv_rev, Units.val_mul, mapc_mul, transpose_mul]
theorem Dual.emb_inv (h : Dual c J X Y) (g : GL k R) :
    embM c J X Y g.1 ((g⁻¹).1.map c)ᵀ * embM c J X Y (g⁻¹).1 ((g⁻¹⁻¹).1.map c)ᵀ = 1 := by
  rw [h.emb_mul, ← star_mul]
  simp [embM, mapc_one]
def Dual.emb (h : Dual c J X Y) : GL k R →* UG c J where
  toFun g := ⟨⟨embM c J X Y g.1 ((g⁻¹).1.map c)ᵀ, embM c J X Y (g⁻¹).1 ((g⁻¹⁻¹).1.map c)ᵀ, h.emb_inv g,
    mul_eq_one_comm.1 (h.emb_inv g)⟩, by
      change (embM c J X Y g.1 ((g⁻¹).1.map c)ᵀ)ᵀ * J * (embM c J X Y g.1 ((g⁻¹).1.map c)ᵀ).map c = J
      have := mul_eq_one_comm.1 (h.emb_inv g)
      rw [inv_inv] at this
      rw [h.emb_tr, Matrix.mul_assoc, ← mapc_mul, this, mapc_one, Matrix.mul_one]⟩
  map_one' := Subtype.ext (Units.ext (by simp [embM]))
  map_mul' g f := Subtype.ext (Units.ext (by
    change embM c J X Y (g.1 * f.1) _ = embM c J X Y g.1 _ * embM c J X Y f.1 _
    rw [h.emb_mul, ← star_mul]))
end PositivityTheory.ThKEnd.Two
end


