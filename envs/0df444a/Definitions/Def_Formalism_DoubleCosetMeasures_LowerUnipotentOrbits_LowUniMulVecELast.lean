-- Prove2me | Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
-- name    : Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:11:26.175834+00:00
-- url     : https://prove2.me/theorems/82b1bbbe-c55d-4fe3-882d-70989a84f1a4
-- title:
--   Low Uni Mul Vec ELast
-- statement:
--   Definitions and structural lemmas for Low Uni Mul Vec ELast, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/LowUniMulVecELast.lean

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
namespace Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
section SlopeTestRemainingChoices
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
def liftR (M : Matrix (Fin n) (Fin n) K) (hM : IsInt R M) : Matrix (Fin n) (Fin n) R :=
  fun i j => ⟨M i j, hM i j⟩
theorem coeLin_apply (v : Fin n → R) (j : Fin n) : coeLin R v j = (v j : K) := by
  rfl
theorem coeLin_mulVec (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    coeLin R (M *ᵥ v) = M.map R.subtype *ᵥ coeLin R v := by
  funext i
  simp [Matrix.mulVec, dotProduct, coeLin_apply]
theorem mem_latZ (Z : Matrix (Fin n) (Fin n) K) (x : Fin n → R) :
    x ∈ latZ R Z ↔ ∃ y, Z *ᵥ coeLin R y = coeLin R x := by
  exact Iff.rfl
theorem det_lift_eq_one (M : Matrix (Fin n) (Fin n) R) (h : (M.map R.subtype).det = 1) :
    M.det = 1 := by
  have h2 : R.subtype M.det = R.subtype 1 := by
    rw [RingHom.map_det, map_one]
    exact h
  exact Subtype.ext h2
end SlopeTestRemainingChoices
section Inv
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
def eqvA (A : Matrix (Fin n) (Fin n) R) (hA : (A.map R.subtype).det = 1) :
    (Fin n → R) ≃ₗ[R] (Fin n → R) :=
  LinearEquiv.ofLinear A.mulVecLin A⁻¹.mulVecLin
    (by
      apply LinearMap.ext; intro v
      simp [mulVec_mulVec, Matrix.mul_nonsing_inv A (by simp [det_lift_eq_one R A hA])])
    (by
      apply LinearMap.ext; intro v
      simp [mulVec_mulVec, Matrix.nonsing_inv_mul A (by simp [det_lift_eq_one R A hA])])
theorem map_latZ (A B : Matrix (Fin n) (Fin n) R) (Z : Matrix (Fin n) (Fin n) K)
    (hA : (A.map R.subtype).det = 1) (hB : (B.map R.subtype).det = 1) :
    (latZ R Z).map (eqvA R A hA : (Fin n → R) →ₗ[R] (Fin n → R)) =
      latZ R (A.map R.subtype * Z * B.map R.subtype) := by
  have hAd := det_lift_eq_one R A hA
  have hBd := det_lift_eq_one R B hB
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (by rw [hAd]; exact isUnit_one)
  have hAA' : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (by rw [hAd]; exact isUnit_one)
  have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B (by rw [hBd]; exact isUnit_one)
  have hAm' : (A⁻¹).map R.subtype * A.map R.subtype = 1 := by
    rw [← Matrix.map_mul, hAA']
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hBm : B.map R.subtype * (B⁻¹).map R.subtype = 1 := by
    rw [← Matrix.map_mul, hBB]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y', hy'⟩ := (mem_latZ R Z y).1 hy
    refine (mem_latZ R _ _).2 ⟨B⁻¹ *ᵥ y', ?_⟩
    show _ = coeLin R (A *ᵥ y)
    rw [coeLin_mulVec, coeLin_mulVec, ← hy', Matrix.mulVec_mulVec, Matrix.mul_assoc, hBm,
      Matrix.mul_one, ← Matrix.mulVec_mulVec]
  · intro hx
    obtain ⟨y', hy'⟩ := (mem_latZ R _ x).1 hx
    refine ⟨A⁻¹ *ᵥ x, (mem_latZ R Z _).2 ⟨B *ᵥ y', ?_⟩, ?_⟩
    · rw [coeLin_mulVec, coeLin_mulVec, ← hy', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hAm', Matrix.one_mul]
    · show A *ᵥ (A⁻¹ *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
def cokEquiv (A B : Matrix (Fin n) (Fin n) R) (Z : Matrix (Fin n) (Fin n) K)
    (hA : (A.map R.subtype).det = 1) (hB : (B.map R.subtype).det = 1) :
    coker R Z ≃ₗ[R] coker R (A.map R.subtype * Z * B.map R.subtype) :=
  Submodule.Quotient.equiv _ _ (eqvA R A hA) (map_latZ R A B Z hA hB)
end Inv
end Formalism.DoubleCosetMeasures.P


