-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block32EqZeroOfUnipotent
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_Block32EqZeroOfUnipotent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:24:56.782061+00:00
-- url     : https://prove2.me/theorems/7da11f43-e2e0-462f-ac0d-516cd6d52659
-- title:
--   Block32 Eq Zero Of Unipotent
-- statement:
--   Definitions and structural lemmas for Block32 Eq Zero Of Unipotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block32EqZeroOfUnipotent.lean

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Minors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.S3x9
open Matrix Finset
open Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni upUniG)
def revRows (A : Type) (r : ℕ) : Matrix (Fin r) (Fin r) A ≃ Matrix (Fin r) (Fin r) A where
  toFun X := X.submatrix Fin.rev id
  invFun X := X.submatrix Fin.rev id
  left_inv X := by ext i j; simp
  right_inv X := by ext i j; simp
theorem block31_add {A : Type} [CommRing A] {r k : ℕ} (x y : Matrix (Idx r k) (Idx r k) A) :
    b31 (x + y) = b31 x + b31 y := rfl
theorem block31_sub {A : Type} [CommRing A] {r k : ℕ} (x y : Matrix (Idx r k) (Idx r k) A) :
    b31 (x - y) = b31 x - b31 y := rfl
def lowerLeftBlockMatrix {A : Type} [Zero A] (r k : ℕ) (Y : Matrix (Fin r) (Fin r) A) : Matrix (Idx r k) (Idx r k) A :=
  Matrix.of fun i j =>
    match i, j with
    | Sum.inr (Sum.inr a), Sum.inl b => Y a b
    | _, _ => 0
theorem block31_lowerLeftBlockMatrix {A : Type} [Zero A] (r k : ℕ) (Y : Matrix (Fin r) (Fin r) A) :
    b31 (lowerLeftBlockMatrix r k Y) = Y := rfl
def splitEquiv (A : Type) [CommRing A] (r k : ℕ) (P : Matrix (Fin r) (Fin r) A → Prop) :
    {M : Matrix (Idx r k) (Idx r k) A // P (b31 M)} ≃
      {Y : Matrix (Fin r) (Fin r) A // P Y} × {Z : Matrix (Idx r k) (Idx r k) A // b31 Z = 0} where
  toFun M := (⟨b31 M.1, M.2⟩, ⟨M.1 - lowerLeftBlockMatrix r k (b31 M.1), by rw [block31_sub, block31_lowerLeftBlockMatrix, sub_self]⟩)
  invFun p := ⟨p.2.1 + lowerLeftBlockMatrix r k p.1.1, by
    rw [block31_add, block31_lowerLeftBlockMatrix, p.2.2, zero_add]; exact p.1.2⟩
  left_inv M := by
    apply Subtype.ext
    simp
  right_inv p := by
    obtain ⟨⟨Y, hY⟩, ⟨Z, hZ⟩⟩ := p
    have h : b31 (Z + lowerLeftBlockMatrix r k Y) = Y := by rw [block31_add, block31_lowerLeftBlockMatrix, hZ, zero_add]
    apply Prod.ext
    · exact Subtype.ext h
    · apply Subtype.ext
      simp [h]
noncomputable def affEquiv {A : Type} [CommRing A] {r : ℕ} (X₀ u : Matrix (Fin r) (Fin r) A)
    (hu : IsUnit u.det) : Matrix (Fin r) (Fin r) A ≃ Matrix (Fin r) (Fin r) A where
  toFun Y := X₀ + u * Y
  invFun X := u⁻¹ * (X - X₀)
  left_inv Y := by
    simp only [add_sub_cancel_left]
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul u hu, Matrix.one_mul]
  right_inv X := by
    simp only
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv u hu, Matrix.one_mul, add_sub_cancel]
end Formalism.FourierDecayAlt.P.S3x9


