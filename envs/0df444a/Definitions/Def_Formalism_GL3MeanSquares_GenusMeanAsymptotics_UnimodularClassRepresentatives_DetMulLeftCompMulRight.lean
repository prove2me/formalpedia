-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DetMulLeftCompMulRight
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DetMulLeftCompMulRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:25:27.123054+00:00
-- url     : https://prove2.me/theorems/ff2bd1dd-2547-45a5-b2d3-a0a648efd77c
-- title:
--   Det Mul Left Comp Mul Right
-- statement:
--   Definitions and structural lemmas for Det Mul Left Comp Mul Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DetMulLeftCompMulRight.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix TensorProduct
namespace Formalism.HermitianLattices.Ext.L3.LITr
section Det
variable {R : Type*} [CommRing R] {m : ℕ}
end Det
section Herm
variable {K F : Type*} [Field K] [CharZero K] [StarRing K] [Field F] [Algebra F K] {m : ℕ}
def hermSub (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (m : ℕ) :
    Submodule F (Matrix (Fin m) (Fin m) K) where
  carrier := {B | Bᴴ = B}
  add_mem' := by
    intro a b ha hb
    change (a + b)ᴴ = a + b
    rw [Matrix.conjTranspose_add, show aᴴ = a from ha, show bᴴ = b from hb]
  zero_mem' := Matrix.conjTranspose_zero
  smul_mem' := by
    intro c B hB
    change (c • B)ᴴ = c • B
    rw [← algebraMap_smul K c B, Matrix.conjTranspose_smul, show Bᴴ = B from hB, (hF _).2 ⟨c, rfl⟩]
variable (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K))
theorem mem_hermSub (B : Matrix (Fin m) (Fin m) K) : B ∈ hermSub hF m ↔ Bᴴ = B := Iff.rfl
noncomputable def toMat (m : ℕ) : K ⊗[F] (hermSub hF m) →ₗ[K] Matrix (Fin m) (Fin m) K :=
  (hermSub hF m).subtype.liftBaseChange K
theorem toMat_tmul (a : K) (B : hermSub hF m) :
    toMat hF m (a ⊗ₜ B) = a • (B : Matrix (Fin m) (Fin m) K) := by
  simp [toMat]
include hF in
theorem exists_decomp {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0) (a : K) :
    ∃ x y : F, a = algebraMap F K x + δ * algebraMap F K y := by
  obtain ⟨x, hx⟩ := (hF ((a + star a) / 2)).1 (by
    rw [star_div₀, star_add, star_star, star_ofNat, add_comm])
  obtain ⟨y, hy⟩ := (hF ((a - star a) / (2 * δ))).1 (by
    rw [star_div₀, star_sub, star_star, star_mul', star_ofNat, hδ]
    field_simp
    ring)
  refine ⟨x, y, ?_⟩
  rw [hx, hy]
  field_simp
  ring
theorem exists_tensor_decomp {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0) (t : K ⊗[F] (hermSub hF m)) :
    ∃ B C : hermSub hF m, t = (1 : K) ⊗ₜ B + δ ⊗ₜ C := by
  induction t with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a B =>
    obtain ⟨x, y, rfl⟩ := exists_decomp hF hδ hδ0 a
    refine ⟨x • B, y • B, ?_⟩
    rw [TensorProduct.add_tmul, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.smul_def, Algebra.smul_def, mul_one,
      mul_comm δ]
  | add s t hs ht =>
    obtain ⟨B, C, rfl⟩ := hs
    obtain ⟨B', C', rfl⟩ := ht
    refine ⟨B + B', C + C', ?_⟩
    rw [TensorProduct.tmul_add, TensorProduct.tmul_add]
    abel
theorem toMat_injective {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0) :
    Function.Injective (toMat hF m) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨B, C, rfl⟩ := exists_tensor_decomp hF hδ hδ0 t
  rw [map_add, toMat_tmul, toMat_tmul, one_smul] at ht
  have ht' := congrArg Matrix.conjTranspose ht
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, (mem_hermSub hF _).1 B.2,
    (mem_hermSub hF _).1 C.2, hδ, Matrix.conjTranspose_zero, neg_smul] at ht'
  have hB : (B : Matrix (Fin m) (Fin m) K) = 0 := by
    have : (2 : K) • (B : Matrix (Fin m) (Fin m) K) = 0 := by
      rw [two_smul]
      calc _ = ((B : Matrix (Fin m) (Fin m) K) + δ • (C : Matrix (Fin m) (Fin m) K)) +
            ((B : Matrix (Fin m) (Fin m) K) + -(δ • (C : Matrix (Fin m) (Fin m) K))) := by abel
        _ = 0 := by rw [ht, ht', add_zero]
    exact (smul_eq_zero.1 this).resolve_left two_ne_zero
  have hC : (C : Matrix (Fin m) (Fin m) K) = 0 := by
    rw [hB, zero_add] at ht
    exact (smul_eq_zero.1 ht).resolve_left hδ0
  rw [Subtype.ext (a1 := B) (a2 := 0) hB, Subtype.ext (a1 := C) (a2 := 0) hC]
  simp
theorem toMat_surjective {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0) :
    Function.Surjective (toMat hF m) := by
  intro X
  have h1 : ((2 : K)⁻¹ • (X + Xᴴ)) ∈ hermSub hF m := by
    rw [mem_hermSub, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, star_inv₀, star_ofNat, add_comm]
  have h2 : ((2 * δ)⁻¹ • (X - Xᴴ)) ∈ hermSub hF m := by
    rw [mem_hermSub, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose, star_inv₀, star_mul', star_ofNat, hδ, mul_neg, inv_neg,
      neg_smul, ← smul_neg, neg_sub]
  refine ⟨(1 : K) ⊗ₜ ⟨_, h1⟩ + δ ⊗ₜ ⟨_, h2⟩, ?_⟩
  rw [map_add, toMat_tmul, toMat_tmul, one_smul, smul_smul]
  have : δ * (2 * δ)⁻¹ = (2 : K)⁻¹ := by field_simp
  rw [this, ← smul_add]
  have : X + Xᴴ + (X - Xᴴ) = (2 : K) • X := by rw [two_smul]; abel
  rw [this, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
noncomputable def toMatEquiv {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0) (m : ℕ) :
    K ⊗[F] (hermSub hF m) ≃ₗ[K] Matrix (Fin m) (Fin m) K :=
  LinearEquiv.ofBijective (toMat hF m) ⟨toMat_injective hF hδ hδ0, toMat_surjective hF hδ hδ0⟩
def conjHerm (P : Matrix (Fin m) (Fin m) K) : hermSub hF m →ₗ[F] hermSub hF m where
  toFun B := ⟨Pᴴ * (B : Matrix (Fin m) (Fin m) K) * P, by
    rw [mem_hermSub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, (mem_hermSub hF _).1 B.2, Matrix.mul_assoc]⟩
  map_add' B C := by
    apply Subtype.ext
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c B := by
    apply Subtype.ext
    simp
end Herm
end Formalism.HermitianLattices.Ext.L3.LITr


