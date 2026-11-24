-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomogeneousIdealOverReesAlgebra
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomogeneousIdealOverReesAlgebra
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:20.709815+00:00
-- url     : https://prove2.me/theorems/94b121c0-751f-406e-9bf5-4f11787eac8b
-- title:
--   Exists Homogeneous Ideal Over Rees Algebra
-- statement:
--   Definitions and structural lemmas for Exists Homogeneous Ideal Over Rees Algebra, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHomogeneousIdealOverReesAlgebra.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id


set_option autoImplicit false
open MvPolynomial
namespace GlobalTheory.ReesHomogeneous
variable {σ : Type} {R : Type} [CommRing R]
theorem homogeneousComponent_mul_of_homogeneous_left {S : Type} [CommRing S] {k : ℕ} (n : ℕ)
    {P : MvPolynomial σ S} (hP : P.IsHomogeneous k) (Q : MvPolynomial σ S) :
    homogeneousComponent n (P * Q) = if k ≤ n then P * homogeneousComponent (n - k) Q else 0 := by
  classical
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := S)
  have h := DirectSum.coe_decompose_mul_of_left_mem (homogeneousSubmodule σ S) (a := P) (b := Q) n
    ((mem_homogeneousSubmodule k P).2 hP)
  have e : ∀ (m : ℕ) (T : MvPolynomial σ S),
      ((DirectSum.decompose (homogeneousSubmodule σ S) T m : homogeneousSubmodule σ S m) :
        MvPolynomial σ S) = homogeneousComponent m T :=
    fun m T => MvPolynomial.decomposition.decompose'_apply T m
  rw [e, e] at h
  exact h
noncomputable def piece (I : Ideal R) (e : ℕ) (F : MvPolynomial σ (reesAlgebra I)) :
    MvPolynomial σ R :=
  ∑ m ∈ F.support, monomial m (((coeff m F : reesAlgebra I) : Polynomial R).coeff e)
variable {I : Ideal R}
@[simp] theorem coeff_piece (e : ℕ) (F : MvPolynomial σ (reesAlgebra I)) (m : σ →₀ ℕ) :
    coeff m (piece I e F) = (coeff m F).1.coeff e := by
  classical
  simp only [piece, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h]; rfl
@[simp] theorem piece_zero (e : ℕ) : piece I e (0 : MvPolynomial σ (reesAlgebra I)) = 0 := by
  ext m; simp
@[simp] theorem piece_add (e : ℕ) (F G : MvPolynomial σ (reesAlgebra I)) :
    piece I e (F + G) = piece I e F + piece I e G := by
  ext m; simp
theorem piece_X_mul (e : ℕ) (i : σ) (F : MvPolynomial σ (reesAlgebra I)) :
    piece I e (X i * F) = X i * piece I e F := by
  classical
  ext m
  rw [coeff_piece, coeff_X_mul', coeff_X_mul']
  split_ifs <;> simp
theorem piece_C_mul (e : ℕ) (r : reesAlgebra I) (F : MvPolynomial σ (reesAlgebra I)) :
    piece I e (C r * F) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal e, C ((r : Polynomial R).coeff p.1) * piece I p.2 F := by
  ext m
  simp [coeff_sum, coeff_C_mul, Polynomial.coeff_mul]
theorem piece_isHomogeneous (e : ℕ) {d : ℕ} {F : MvPolynomial σ (reesAlgebra I)}
    (hF : F.IsHomogeneous d) : (piece I e F).IsHomogeneous d := by
  intro m hm
  apply hF
  intro h
  apply hm
  rw [coeff_piece, h]
  simp
theorem coeff_piece_mem (e : ℕ) (F : MvPolynomial σ (reesAlgebra I)) (m : σ →₀ ℕ) :
    coeff m (piece I e F) ∈ I ^ e := by
  rw [coeff_piece]
  exact (mem_reesAlgebra_iff I _).1 (coeff m F).2 e
end GlobalTheory.ReesHomogeneous
namespace GlobalTheory.ReesHomogeneous
variable {σ : Type} {R : Type} [CommRing R] {I : Ideal R}
theorem C_mul_mem_of_pow (J : ℕ → Ideal (MvPolynomial σ R))
    (H : ∀ (e t : ℕ) (a : R) (F : MvPolynomial σ R), a ∈ I → F.IsHomogeneous t →
      (∀ m, coeff m F ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) :
    ∀ (k : ℕ) (b : R), b ∈ I ^ k → ∀ (l t : ℕ) (P : MvPolynomial σ R), P.IsHomogeneous t →
      (∀ m, coeff m P ∈ I ^ l) → P ∈ J l → C b * P ∈ J (l + k) := by
  intro k
  induction k with
  | zero =>
    intro b _ l t P _ _ hP
    simpa using (J l).mul_mem_left (C b) hP
  | succ k ih =>
    intro b hb l t P hPh hPc hP
    rw [pow_succ] at hb
    refine Submodule.mul_induction_on hb ?_ ?_
    · intro x hx y hy
      have h1 := ih x hx l t P hPh hPc hP
      have h2 : ∀ m, coeff m (C x * P) ∈ I ^ (l + k) := by
        intro m
        rw [coeff_C_mul, pow_add, mul_comm (I ^ l)]
        exact Ideal.mul_mem_mul hx (hPc m)
      have h3 := H (l + k) t y (C x * P) hy (hPh.C_mul x) h2 h1
      rw [show C (x * y) * P = C y * (C x * P) by rw [C_mul]; ring]
      simpa [add_assoc] using h3
    · intro x y hx hy
      rw [C_add, add_mul]
      exact add_mem hx hy
def reesIdeal (I : Ideal R) (J : ℕ → Ideal (MvPolynomial σ R))
    (H : ∀ (e t : ℕ) (a : R) (F : MvPolynomial σ R), a ∈ I → F.IsHomogeneous t →
      (∀ m, coeff m F ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) :
    Ideal (MvPolynomial σ (reesAlgebra I)) where
  carrier := {F | ∀ d e, piece I e (homogeneousComponent d F) ∈ J e}
  zero_mem' := by intro d e; simp
  add_mem' := by
    intro F G hF hG d e
    rw [map_add, piece_add]
    exact add_mem (hF d e) (hG d e)
  smul_mem' := by
    intro c F hF
    rw [smul_eq_mul]
    revert F
    induction c using MvPolynomial.induction_on with
    | C r =>
      intro F hF d e
      rw [homogeneousComponent_C_mul, piece_C_mul]
      refine Ideal.sum_mem _ fun p hp => ?_
      have hpe : p.2 + p.1 = e := by rw [add_comm]; exact Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      rw [← hpe]
      exact C_mul_mem_of_pow J H p.1 _ ((mem_reesAlgebra_iff I _).1 r.2 p.1) p.2 d _
        (piece_isHomogeneous p.2 (homogeneousComponent_isHomogeneous d F))
        (coeff_piece_mem p.2 _) (hF d p.2)
    | add p q hp hq =>
      intro F hF d e
      rw [add_mul, map_add, piece_add]
      exact add_mem (hp hF d e) (hq hF d e)
    | mul_X p i hp =>
      intro F hF
      rw [mul_assoc]
      apply hp
      intro d e
      rw [homogeneousComponent_mul_of_homogeneous_left d (isHomogeneous_X _ i)]
      split_ifs
      · rw [piece_X_mul]
        exact (J e).mul_mem_left _ (hF _ e)
      · simp
end GlobalTheory.ReesHomogeneous
namespace GlobalTheory.ReesHomogeneous
end GlobalTheory.ReesHomogeneous


