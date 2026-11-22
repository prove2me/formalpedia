-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:21:18.484278+00:00
-- url     : https://prove2.me/theorems/ade04a81-f4f5-404b-88a6-9020d10daaf7
-- title:
--   Pointwise Stabiliser Parametrisation Bijective
-- statement:
--   Definitions and structural lemmas for Pointwise Stabiliser Parametrisation Bijective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointwiseStabiliserParametrisationBijective.lean

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Formalism.FourierDecayAlt.P.S3x1
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3
section Blocks
variable {A : Type} {r k : ℕ}
variable [CommRing A]
theorem block11_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b11 (x * y) = b11 x * b11 y + b12 x * b21 y + b13 x * b31 y := by
  ext a b
  simp [b11, b11, b12, b13, b11, b21, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]
theorem one_block11 : b11 (1 : Matrix (Idx r k) (Idx r k) A) = 1 := by
  ext a b
  simp [b11, Matrix.one_apply]
theorem block12_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b12 (x * y) = b11 x * b12 y + b12 x * b22 y + b13 x * b32 y := by
  ext a b
  simp [b12, b11, b12, b13, b12, b22, b32, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]
theorem block12_one : b12 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b12, Matrix.one_apply]
theorem block21_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b21 (x * y) = b21 x * b11 y + b22 x * b21 y + b23 x * b31 y := by
  ext a b
  simp [b21, b21, b22, b23, b11, b21, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]
theorem one_block21 : b21 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b21, Matrix.one_apply]
theorem block22_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b22 (x * y) = b21 x * b12 y + b22 x * b22 y + b23 x * b32 y := by
  ext a b
  simp [b22, b21, b22, b23, b12, b22, b32, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]
theorem block22_one : b22 (1 : Matrix (Idx r k) (Idx r k) A) = 1 := by
  ext a b
  simp [b22, Matrix.one_apply]
theorem block23_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b23 (x * y) = b21 x * b13 y + b22 x * b23 y + b23 x * b33 y := by
  ext a b
  simp [b23, b21, b22, b23, b13, b23, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]
theorem block23_one : b23 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b23, Matrix.one_apply]
theorem block31_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b31 (x * y) = b31 x * b11 y + b32 x * b21 y + b33 x * b31 y := by
  ext a b
  simp [b31, b31, b32, b33, b11, b21, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]
theorem one_block31 : b31 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b31, Matrix.one_apply]
theorem block32_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b32 (x * y) = b31 x * b12 y + b32 x * b22 y + b33 x * b32 y := by
  ext a b
  simp [b32, b31, b32, b33, b12, b22, b32, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]
theorem block32_one : b32 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b32, Matrix.one_apply]
theorem block33_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b33 (x * y) = b31 x * b13 y + b32 x * b23 y + b33 x * b33 y := by
  ext a b
  simp [b33, b31, b32, b33, b13, b23, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]
theorem block33_one : b33 (1 : Matrix (Idx r k) (Idx r k) A) = 1 := by
  ext a b
  simp [b33, Matrix.one_apply]
theorem midEmb_mul (h h' : Matrix (Fin k) (Fin k) A) : midEmb h * midEmb h' = midEmb (h * h') := by
  simp [midEmb, Matrix.fromBlocks_multiply]
theorem midEmb_one : midEmb (1 : Matrix (Fin k) (Fin k) A) = 1 := by
  simp [midEmb]
theorem midEmb_det (h : Matrix (Fin k) (Fin k) A) : (midEmb h).det = h.det := by
  simp [midEmb]
theorem levi_embedding_block11 (h : Matrix (Fin k) (Fin k) A) : b11 (hEmb r h) = 1 := by
  ext a b; simp [b11, hEmb]
theorem levi_embedding_block12 (h : Matrix (Fin k) (Fin k) A) : b12 (hEmb r h) = 0 := by
  ext a b; simp [b12, hEmb]
theorem levi_embedding_block13 (h : Matrix (Fin k) (Fin k) A) : b13 (hEmb r h) = 0 := by
  ext a b; simp [b13, hEmb]
theorem levi_embedding_block21 (h : Matrix (Fin k) (Fin k) A) : b21 (hEmb r h) = 0 := by
  ext a b; simp [b21, hEmb]
theorem levi_embedding_block22 (h : Matrix (Fin k) (Fin k) A) : b22 (hEmb r h) = midEmb h := by
  ext a b; simp [b22, hEmb]
theorem levi_embedding_block23 (h : Matrix (Fin k) (Fin k) A) : b23 (hEmb r h) = 0 := by
  ext a b; simp [b23, hEmb]
theorem levi_embedding_block31 (h : Matrix (Fin k) (Fin k) A) : b31 (hEmb r h) = 0 := by
  ext a b; simp [b31, hEmb]
theorem levi_embedding_block32 (h : Matrix (Fin k) (Fin k) A) : b32 (hEmb r h) = 0 := by
  ext a b; simp [b32, hEmb]
theorem levi_embedding_block33 (h : Matrix (Fin k) (Fin k) A) : b33 (hEmb r h) = 1 := by
  ext a b; simp [b33, hEmb]
theorem hEmb_mul (h h' : Matrix (Fin k) (Fin k) A) : hEmb r h * hEmb r h' = hEmb r (h * h') := by
  simp [hEmb, Matrix.fromBlocks_multiply, midEmb_mul]
theorem hEmb_one : hEmb r (1 : Matrix (Fin k) (Fin k) A) = 1 := by
  simp [hEmb, midEmb_one]
theorem lcancel {n m : Type} [Fintype n] [DecidableEq n] {f : Matrix n n A} (hf : IsUnit f.det)
    {Y Z : Matrix n m A} (h : f * Y = f * Z) : Y = Z := by
  rw [← Matrix.nonsing_inv_mul_cancel_left f Y hf, h, Matrix.nonsing_inv_mul_cancel_left f Z hf]
structure GP (P : Matrix (Fin k) (Fin k) A → Prop) : Prop where
  one : P 1
  mul : ∀ {h h'}, P h → P h' → P (h * h')
  inv : ∀ {h}, P h → P h⁻¹
  unit : ∀ {h}, P h → IsUnit h.det
theorem gpUnit : GP (fun h : Matrix (Fin k) (Fin k) A => IsUnit h.det) where
  one := by simp
  mul := by intro h h' a b; rw [Matrix.det_mul]; exact a.mul b
  inv := by intro h a; exact Matrix.isUnit_nonsing_inv_det h a
  unit := fun a => a
def Par (P : Matrix (Fin k) (Fin k) A → Prop) (x : Matrix (Idx r k) (Idx r k) A) : Prop :=
  IsUpUni (b11 x) ∧ IsUpUni (b33 x) ∧ b21 x = 0 ∧ b31 x = 0 ∧ b32 x = 0 ∧ ∃ h, P h ∧ b22 x = midEmb h
def Emb (P : Matrix (Fin k) (Fin k) A → Prop) (x : Matrix (Idx r k) (Idx r k) A) : Prop :=
  ∃ h, P h ∧ x = hEmb r h
variable {P : Matrix (Fin k) (Fin k) A → Prop}
theorem uni_unit {n : ℕ} {u : Matrix (Fin n) (Fin n) A} (hu : IsUpUni u) : IsUnit u.det := by
  rw [isUpUni_det A hu]; exact isUnit_one
theorem par_one (hP : GP P) : Par P (1 : Matrix (Idx r k) (Idx r k) A) :=
  ⟨by rw [one_block11]; exact isUpUni_one A, by rw [block33_one]; exact isUpUni_one A, one_block21, one_block31,
    block32_one, 1, hP.one, by rw [block22_one, midEmb_one]⟩
theorem par_mul (hP : GP P) {x y : Matrix (Idx r k) (Idx r k) A} (hx : Par P x) (hy : Par P y) :
    Par P (x * y) := by
  obtain ⟨h11, h33, h21, h31, h32, h, hh, h22⟩ := hx
  obtain ⟨g11, g33, g21, g31, g32, g, hg, g22⟩ := hy
  refine ⟨?_, ?_, ?_, ?_, ?_, h * g, hP.mul hh hg, ?_⟩
  · rw [block11_mul, g21, g31]; simpa using isUpUni_mul A h11 g11
  · rw [block33_mul, h31, h32]; simpa using isUpUni_mul A h33 g33
  · rw [block21_mul, h21, g21, g31]; simp
  · rw [block31_mul, h31, h32, g31]; simp
  · rw [block32_mul, h31, h32, g32]; simp
  · rw [block22_mul, h21, g32, h22, g22, midEmb_mul]; simp
theorem par_rinv (hP : GP P) {x y : Matrix (Idx r k) (Idx r k) A} (hx : Par P x) (e : x * y = 1) :
    Par P y := by
  obtain ⟨h11, h33, h21, h31, h32, h, hh, h22⟩ := hx
  have um : IsUnit (midEmb h).det := by rw [midEmb_det]; exact hP.unit hh
  have y31 : b31 y = 0 := by
    have := block31_mul x y
    rw [e, one_block31, h31, h32] at this
    exact lcancel (uni_unit h33) (by simpa using this.symm)
  have y32 : b32 y = 0 := by
    have := block32_mul x y
    rw [e, block32_one, h31, h32] at this
    exact lcancel (uni_unit h33) (by simpa using this.symm)
  have y33 : b33 y = (b33 x)⁻¹ := by
    have := block33_mul x y
    rw [e, block33_one, h31, h32] at this
    exact (Matrix.inv_eq_right_inv (by simpa using this.symm)).symm
  have y21 : b21 y = 0 := by
    have := block21_mul x y
    rw [e, one_block21, h21, y31, h22] at this
    exact lcancel um (by simpa using this.symm)
  have y22 : b22 y = midEmb h⁻¹ := by
    have := block22_mul x y
    rw [e, block22_one, h21, y32, h22] at this
    refine lcancel um ?_
    rw [midEmb_mul, Matrix.mul_nonsing_inv h (hP.unit hh), midEmb_one]
    simpa using this.symm
  have y11 : b11 y = (b11 x)⁻¹ := by
    have := block11_mul x y
    rw [e, one_block11, y21, y31] at this
    exact (Matrix.inv_eq_right_inv (by simpa using this.symm)).symm
  exact ⟨y11 ▸ isUpUni_inv A h11, y33 ▸ isUpUni_inv A h33, y21, y31, y32, h⁻¹, hP.inv hh, y22⟩
def parG (hP : GP P) : Subgroup (GL (Idx r k) A) where
  carrier := {g | Par P (g : Matrix (Idx r k) (Idx r k) A)}
  one_mem' := by simpa using par_one hP
  mul_mem' := by intro a b ha hb; simpa using par_mul hP ha hb
  inv_mem' := by
    intro a ha
    refine par_rinv hP ha ?_
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
def embG (hP : GP P) : Subgroup (GL (Idx r k) A) where
  carrier := {g | Emb P (g : Matrix (Idx r k) (Idx r k) A)}
  one_mem' := ⟨1, hP.one, by simp [hEmb_one]⟩
  mul_mem' := by
    rintro a b ⟨h, hh, ea⟩ ⟨g, hg, eb⟩
    exact ⟨h * g, hP.mul hh hg, by rw [Units.val_mul, ea, eb, hEmb_mul]⟩
  inv_mem' := by
    rintro a ⟨h, hh, ea⟩
    refine ⟨h⁻¹, hP.inv hh, ?_⟩
    rw [Matrix.coe_units_inv, ea]
    refine Matrix.inv_eq_right_inv ?_
    rw [hEmb_mul, Matrix.mul_nonsing_inv h (hP.unit hh), hEmb_one]
theorem prod_iff (hP : GP P) (x : Matrix (Idx r k) (Idx r k) A) :
    (∃ n u, IsN n ∧ Emb P u ∧ x = n * u) ↔ Par P x := by
  constructor
  · rintro ⟨n, _, ⟨h11, h33, h22, h21, h31, h32⟩, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, h, hh, ?_⟩
    · rw [block11_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31]; simpa using h11
    · rw [block33_mul, levi_embedding_block13, levi_embedding_block23, levi_embedding_block33]; simpa using h33
    · rw [block21_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31, h21]; simp
    · rw [block31_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31, h31]; simp
    · rw [block32_mul, levi_embedding_block12, levi_embedding_block22, levi_embedding_block32, h32]; simp
    · rw [block22_mul, levi_embedding_block12, levi_embedding_block22, levi_embedding_block32, h22]; simp
  · rintro ⟨h11, h33, h21, h31, h32, h, hh, h22⟩
    refine ⟨x * hEmb r h⁻¹, hEmb r h, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨h, hh, rfl⟩, ?_⟩
    · rw [block11_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31]; simpa using h11
    · rw [block33_mul, levi_embedding_block13, levi_embedding_block23, levi_embedding_block33]; simpa using h33
    · rw [block22_mul, levi_embedding_block12, levi_embedding_block22, levi_embedding_block32, h22, midEmb_mul,
        Matrix.mul_nonsing_inv h (hP.unit hh), midEmb_one]; simp
    · rw [block21_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31, h21]; simp
    · rw [block31_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31, h31]; simp
    · rw [block32_mul, levi_embedding_block12, levi_embedding_block22, levi_embedding_block32, h32]; simp
    · rw [Matrix.mul_assoc, hEmb_mul, Matrix.nonsing_inv_mul h (hP.unit hh), hEmb_one, Matrix.mul_one]
theorem isS_iff (x : Matrix (Idx r k) (Idx r k) A) : IsS x ↔ Par (fun h => IsUnit h.det) x :=
  prod_iff gpUnit x
theorem mul_midEmb_last {m : Type} (M : Matrix m (Mid k) A) (h : Matrix (Fin k) (Fin k) A) (a : m) :
    (M * midEmb h) a (Sum.inr ()) = M a (Sum.inr ()) := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, midEmb]
theorem midEmb_mul_last {m : Type} (M : Matrix (Mid k) m A) (h : Matrix (Fin k) (Fin k) A) (b : m) :
    (midEmb h * M) (Sum.inr ()) b = M (Sum.inr ()) b := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, midEmb]
theorem mem_pointwise_stabiliser_iff (x : Matrix (Idx r k) (Idx r k) A) : IsInertiaInfiniteCyclotomic x ↔ Par (fun h => IsUnit h.det) x ∧
    b11 x = 1 ∧ b33 x = 1 ∧ (∀ a, b12 x a (Sum.inr ()) = 0) ∧ ∀ b, b23 x (Sum.inr ()) b = 0 := by
  unfold IsInertiaInfiniteCyclotomic; rw [isS_iff]
theorem pointwise_stabiliser_one_mem : IsInertiaInfiniteCyclotomic (1 : Matrix (Idx r k) (Idx r k) A) := by
  rw [mem_pointwise_stabiliser_iff]
  exact ⟨par_one gpUnit, one_block11, block33_one, by simp [block12_one], by simp [block23_one]⟩
theorem pointwise_stabiliser_mul_mem {x y : Matrix (Idx r k) (Idx r k) A} (hx : IsInertiaInfiniteCyclotomic x) (hy : IsInertiaInfiniteCyclotomic y) : IsInertiaInfiniteCyclotomic (x * y) := by
  rw [mem_pointwise_stabiliser_iff] at hx hy ⊢
  obtain ⟨px, x11, x33, x12, x23⟩ := hx
  obtain ⟨py, y11, y33, y12, y23⟩ := hy
  refine ⟨par_mul gpUnit px py, ?_, ?_, ?_, ?_⟩
  · obtain ⟨-, -, g21, g31, -⟩ := py
    rw [block11_mul, g21, g31, x11, y11]; simp
  · obtain ⟨-, -, -, h31, h32, -⟩ := px
    rw [block33_mul, h31, h32, x33, y33]; simp
  · intro a
    obtain ⟨-, -, -, -, g32, g, -, g22⟩ := py
    rw [block12_mul, g32, g22, x11]
    simp [Matrix.add_apply, mul_midEmb_last, x12, y12]
  · intro b
    obtain ⟨-, -, h21, -, -, h, -, h22⟩ := px
    rw [block23_mul, h21, h22, y33]
    simp [Matrix.add_apply, midEmb_mul_last, x23, y23]
theorem pointwise_stabiliser_right_inverse_mem {x y : Matrix (Idx r k) (Idx r k) A} (hx : IsInertiaInfiniteCyclotomic x) (e : x * y = 1) : IsInertiaInfiniteCyclotomic y := by
  rw [mem_pointwise_stabiliser_iff] at hx ⊢
  obtain ⟨px, x11, x33, x12, x23⟩ := hx
  have py := par_rinv gpUnit px e
  obtain ⟨-, -, h21, h31, h32, h, -, h22⟩ := px
  obtain ⟨-, -, g21, g31, g32, g, -, g22⟩ := id py
  have y11 : b11 y = 1 := by
    have := block11_mul x y
    rw [e, one_block11, g21, g31, x11] at this
    simpa using this.symm
  have y33 : b33 y = 1 := by
    have := block33_mul x y
    rw [e, block33_one, h31, h32, x33] at this
    simpa using this.symm
  refine ⟨py, y11, y33, ?_, ?_⟩
  · intro a
    have := congrFun (congrFun (block12_mul x y) a) (Sum.inr ())
    rw [e, block12_one, g32, g22, x11] at this
    simpa [Matrix.add_apply, mul_midEmb_last, x12] using this.symm
  · intro b
    have := congrFun (congrFun (block23_mul x y) (Sum.inr ())) b
    rw [e, block23_one, h21, h22, y33] at this
    simpa [Matrix.add_apply, midEmb_mul_last, x23] using this.symm
def s0G : Subgroup (GL (Idx r k) A) where
  carrier := {g | IsInertiaInfiniteCyclotomic (g : Matrix (Idx r k) (Idx r k) A)}
  one_mem' := by simpa using pointwise_stabiliser_one_mem
  mul_mem' := by intro a b ha hb; simpa using pointwise_stabiliser_mul_mem ha hb
  inv_mem' := by
    intro a ha
    refine pointwise_stabiliser_right_inverse_mem ha ?_
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
end Blocks
end Formalism.FourierDecayAlt.P.S3x1
namespace Formalism.FourierDecayAlt.P.S3x1
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
theorem block11_of_blocks : b11 (mk a b c m e f) = a := by ext i j; simp [b11, mk]
theorem block12_of_blocks : b12 (mk a b c m e f) = b := by ext i j; simp [b12, mk]
theorem block21_of_blocks : b21 (mk a b c m e f) = 0 := by ext i j; simp [b21, mk]
theorem block22_of_blocks : b22 (mk a b c m e f) = m := by ext i j; simp [b22, mk]
theorem block23_of_blocks : b23 (mk a b c m e f) = e := by ext i j; simp [b23, mk]
theorem block31_of_blocks : b31 (mk a b c m e f) = 0 := by ext i j; simp [b31, mk]
theorem block32_of_blocks : b32 (mk a b c m e f) = 0 := by ext i j; simp [b32, mk]
theorem block33_of_blocks : b33 (mk a b c m e f) = f := by ext i j; simp [b33, mk]
end mk
def parMap (P : Matrix (Fin k) (Fin k) A → Prop) :
    ({a : Matrix (Fin r) (Fin r) A // IsUpUni a} × {f : Matrix (Fin r) (Fin r) A // IsUpUni f} ×
      {h : Matrix (Fin k) (Fin k) A // P h} × Matrix (Fin r) (Mid k) A × Matrix (Fin r) (Fin r) A ×
      Matrix (Mid k) (Fin r) A) → {x : Matrix (Idx r k) (Idx r k) A // Par P x} :=
  fun t => ⟨mk t.1.1 t.2.2.2.1 t.2.2.2.2.1 (midEmb t.2.2.1.1) t.2.2.2.2.2 t.2.1.1,
    by rw [block11_of_blocks]; exact t.1.2, by rw [block33_of_blocks]; exact t.2.1.2, block21_of_blocks .., block31_of_blocks .., block32_of_blocks ..,
    t.2.2.1.1, t.2.2.1.2, block22_of_blocks ..⟩
end Count
end Formalism.FourierDecayAlt.P.S3x1
namespace Formalism.FourierDecayAlt.P.S3x1
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3
section Count2
variable {A : Type} [CommRing A] {r k : ℕ}
def pointwiseStabiliserParametrisation : ({h : Matrix (Fin k) (Fin k) A // IsUnit h.det} × Matrix (Fin r) (Fin k) A ×
      Matrix (Fin r) (Fin r) A × Matrix (Fin k) (Fin r) A) →
    {x : Matrix (Idx r k) (Idx r k) A // IsInertiaInfiniteCyclotomic x} :=
  fun t => ⟨mk 1 (Matrix.fromCols t.2.1 0) t.2.2.1 (midEmb t.1.1) (Matrix.fromRows t.2.2.2 0) 1,
    (mem_pointwise_stabiliser_iff _).2 ⟨⟨by rw [block11_of_blocks]; exact isUpUni_one A, by rw [block33_of_blocks]; exact isUpUni_one A,
      block21_of_blocks .., block31_of_blocks .., block32_of_blocks .., t.1.1, t.1.2, block22_of_blocks ..⟩, block11_of_blocks .., block33_of_blocks ..,
      by intro a; rw [block12_of_blocks]; simp, by intro b; rw [block23_of_blocks]; simp⟩⟩
end Count2
end Formalism.FourierDecayAlt.P.S3x1


