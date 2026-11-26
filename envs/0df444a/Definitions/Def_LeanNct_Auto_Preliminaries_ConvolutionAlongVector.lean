-- Prove2me | Definitions.Def_LeanNct_Auto_Preliminaries_ConvolutionAlongVector
-- name    : LeanNct_Auto_Preliminaries_ConvolutionAlongVector
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T15:37:23.024446+00:00
-- url     : https://prove2.me/theorems/8694d844-6acf-4170-9092-9a03f475f4ac
-- title:
--   Convolution Along Vector
-- statement:
--   Definitions and structural lemmas for Convolution Along Vector, from Floris van Doorn, Polona Durcik, Joris Roos, Lenka Slavíková, Christoph Thiele (roos-j/lean-nct; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Norm-variation of multiple ergodic averages for commuting transformations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/ConvolutionAlongVector.lean

module
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Auto
open MeasureTheory Metric
open scoped FourierTransform RealInnerProductSpace
noncomputable def convolutionAlongVector {n : ℕ} {𝕜 : Type*} [NormedField 𝕜]
    [NormedSpace ℝ 𝕜]
    (rho : EuclideanSpace ℝ (Fin n) → 𝕜) (phi : ℝ → 𝕜)
    (alpha : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) → 𝕜 :=
  fun x ↦ ∫ p : ℝ, rho (x - p • alpha) * phi p
noncomputable def aux_shear {n : ℕ} (alpha : EuclideanSpace ℝ (Fin n)) :
    (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin n) × ℝ) where
  toFun := fun xp ↦ (xp.1 - xp.2 • alpha, xp.2)
  invFun := fun xp ↦ (xp.1 + xp.2 • alpha, xp.2)
  left_inv := by
    rintro ⟨x, p⟩
    ext <;> simp [sub_eq_add_neg]
  right_inv := by
    rintro ⟨x, p⟩
    ext <;> simp [sub_eq_add_neg]
  map_add' := by
    rintro ⟨x, p⟩ ⟨y, q⟩
    ext <;> simp [sub_eq_add_neg, add_smul]; abel
  map_smul' := by
    rintro r ⟨x, p⟩
    ext <;> simp [sub_eq_add_neg, smul_add, smul_smul]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop
end Auto


