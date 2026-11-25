-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_RealSignature
-- name    : GroundTheory_HeightsAndTheta_Theta_RealSignature
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T01:55:33.539801+00:00
-- url     : https://prove2.me/theorems/2b86a9cc-59e5-4dda-b513-a45f505d21e4
-- title:
--   Real Signature
-- statement:
--   Definitions and structural lemmas for Real Signature, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/RealSignature.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] GroundTheory.Automorphic.conjCME_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a


set_option autoImplicit false
namespace GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
omit [Fintype ι] [DecidableEq ι] in

theorem map_starRingEnd_transpose (M : Matrix ι ι ℂ) : (M.map (starRingEnd ℂ))ᵀ = Mᴴ := by
  ext i j
  simp
theorem mem_unitaryGroupMatrix_star_iff {g : GL ι ℂ} :
    g ∈ unitaryGroupMatrix (starRingEnd ℂ) H ↔
      (g : Matrix ι ι ℂ)ᴴ * H * (g : Matrix ι ι ℂ) = H := by
  rw [mem_unitaryGroupMatrix, map_starRingEnd_transpose]
variable (hH : H.IsHermitian)
noncomputable def posEigenCount : ℕ := Fintype.card {i // 0 < hH.eigenvalues i}
noncomputable def negEigenCount : ℕ := Fintype.card {i // hH.eigenvalues i < 0}
variable {hH}
theorem eigenvalues_ne_zero (hu : IsUnit H.det) (i : ι) : hH.eigenvalues i ≠ 0 := by
  intro h0
  rw [hH.det_eq_prod_eigenvalues] at hu
  apply hu.ne_zero
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h0])
noncomputable def signEquiv (hu : IsUnit H.det) : ι ≃ Fin (posEigenCount hH) ⊕ Fin (negEigenCount hH) :=
  (Equiv.sumCompl (fun i => 0 < hH.eigenvalues i)).symm.trans
    (Equiv.sumCongr (Fintype.equivFin _)
      ((Equiv.subtypeEquivRight fun i => by
          have := eigenvalues_ne_zero (hH := hH) hu i
          constructor
          · intro h; exact lt_of_le_of_ne (not_lt.1 h) this
          · intro h; exact not_lt.2 h.le).trans (Fintype.equivFin _)))
theorem sign_eigenvalues_signEquiv_symm (hu : IsUnit H.det) (k : Fin (posEigenCount hH) ⊕ Fin (negEigenCount hH)) :
    (hH.eigenvalues ((signEquiv hu).symm k) / |hH.eigenvalues ((signEquiv hu).symm k)| : ℝ) =
      Sum.elim (fun _ => (1 : ℝ)) (fun _ => -1) k := by
  rcases k with a | b
  · have h : 0 < hH.eigenvalues ((signEquiv hu).symm (Sum.inl a)) := by
      simp only [signEquiv, Equiv.symm_trans_apply]
      exact ((Fintype.equivFin _).symm a).2
    rw [abs_of_pos h, div_self h.ne']
    rfl
  · have h : hH.eigenvalues ((signEquiv hu).symm (Sum.inr b)) < 0 := by
      simp only [signEquiv, Equiv.symm_trans_apply]
      exact (((Fintype.equivFin _).symm b : {i // hH.eigenvalues i < 0})).2
    rw [abs_of_neg h, div_neg, div_self h.ne]
    rfl
theorem star_eigenvectorUnitary_mul_mul (hH : H.IsHermitian) :
    star (hH.eigenvectorUnitary : Matrix ι ι ℂ) * H * (hH.eigenvectorUnitary : Matrix ι ι ℂ) =
      diagonal (fun i => (hH.eigenvalues i : ℂ)) := by
  set U := (hH.eigenvectorUnitary : Matrix ι ι ℂ)
  have h1 : star U * U = 1 := Unitary.coe_star_mul_self _
  conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
  change star U * (U * _ * star U) * U = _
  calc star U * (U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U) * U
      = (star U * U) * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * (star U * U) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.one_mul, Matrix.mul_one]; rfl
theorem exists_congr_indefJ (hu : IsUnit H.det) :
    ∃ (P : Matrix ι (Fin (posEigenCount hH) ⊕ Fin (negEigenCount hH)) ℂ)
      (Q : Matrix (Fin (posEigenCount hH) ⊕ Fin (negEigenCount hH)) ι ℂ),
      Q * P = 1 ∧ P * Q = 1 ∧ Pᴴ * H * P = indefJ (posEigenCount hH) (negEigenCount hH) := by
  set U := (hH.eigenvectorUnitary : Matrix ι ι ℂ)
  set lam := hH.eigenvalues
  have hl : ∀ i, lam i ≠ 0 := eigenvalues_ne_zero hu
  have hs : ∀ i, 0 < Real.sqrt |lam i| := fun i => Real.sqrt_pos.2 (abs_pos.2 (hl i))
  set d : ι → ℂ := fun i => ((Real.sqrt |lam i|)⁻¹ : ℝ)
  set d' : ι → ℂ := fun i => (Real.sqrt |lam i| : ℝ)
  have hdd : ∀ i, d' i * d i = 1 := fun i => by
    simp only [d, d', ← Complex.ofReal_mul, mul_inv_cancel₀ (hs i).ne', Complex.ofReal_one]
  have hdd' : ∀ i, d i * d' i = 1 := fun i => by rw [mul_comm]; exact hdd i
  have h1 : star U * U = 1 := Unitary.coe_star_mul_self _
  have h2 : U * star U = 1 := Unitary.coe_mul_star_self _
  set e := signEquiv (hH := hH) hu
  set P0 := U * diagonal d
  set Q0 := diagonal d' * star U
  have hQP : Q0 * P0 = 1 := by
    calc Q0 * P0 = diagonal d' * (star U * U) * diagonal d := by simp only [Q0, P0, Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact hdd i
  have hPQ : P0 * Q0 = 1 := by
    calc P0 * Q0 = U * (diagonal d * diagonal d') * star U := by simp only [Q0, P0, Matrix.mul_assoc]
      _ = 1 := by
        rw [diagonal_mul_diagonal]
        have : (fun i => d i * d' i) = fun _ => 1 := funext hdd'
        rw [this, diagonal_one, Matrix.mul_one, h2]
  have hPHP : P0ᴴ * H * P0 = diagonal (fun i => ((lam i / |lam i| : ℝ) : ℂ)) := by
    have hdh : (diagonal d)ᴴ = diagonal d := by
      rw [diagonal_conjTranspose]
      congr 1
      funext i
      simp [d]
    calc P0ᴴ * H * P0 = diagonal d * (star U * H * U) * diagonal d := by
          simp only [P0, conjTranspose_mul, hdh, star_eq_conjTranspose, Matrix.mul_assoc]
      _ = _ := by
          rw [star_eigenvectorUnitary_mul_mul, diagonal_mul_diagonal, diagonal_mul_diagonal]
          congr 1
          funext i
          simp only [d]
          have hsq : Real.sqrt |lam i| * Real.sqrt |lam i| = |lam i| :=
            Real.mul_self_sqrt (abs_nonneg _)
          rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
          congr 1
          calc (Real.sqrt |lam i|)⁻¹ * lam i * (Real.sqrt |lam i|)⁻¹
              = lam i * ((Real.sqrt |lam i|)⁻¹ * (Real.sqrt |lam i|)⁻¹) := by ring
            _ = lam i * (Real.sqrt |lam i| * Real.sqrt |lam i|)⁻¹ := by rw [mul_inv]
            _ = lam i / |lam i| := by rw [hsq, div_eq_mul_inv]
  refine ⟨P0.submatrix id e.symm, Q0.submatrix e.symm id, ?_, ?_, ?_⟩
  · rw [← submatrix_mul Q0 P0 e.symm id e.symm Function.bijective_id, hQP, submatrix_one_equiv]
  · rw [submatrix_mul_equiv P0 Q0 id e.symm id, hPQ, submatrix_id_id]
  · rw [conjTranspose_submatrix]
    have e1 := submatrix_mul P0ᴴ H e.symm id id Function.bijective_id
    rw [submatrix_id_id] at e1
    rw [← e1, ← submatrix_mul (P0ᴴ * H) P0 e.symm id e.symm Function.bijective_id, hPHP,
      submatrix_diagonal_equiv, indefJ]
    congr 1
    funext k
    simp only [Function.comp_apply]
    rw [sign_eigenvalues_signEquiv_symm hu k]
    rcases k with a | b <;> simp
section Congr
variable {κ : Type*} [Fintype κ] [DecidableEq κ] {P : Matrix ι κ ℂ} {Q : Matrix κ ι ℂ}
  {H' : Matrix κ κ ℂ}
def congrUnitary (hQP : Q * P = 1) (hPQ : P * Q = 1) (hH' : Pᴴ * H * P = H')
    (g : unitaryGroupMatrix (starRingEnd ℂ) H) : unitaryGroupMatrix (starRingEnd ℂ) H' :=
  ⟨⟨Q * ((g : GL ι ℂ) : Matrix ι ι ℂ) * P, Q * (((g : GL ι ℂ)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) * P,
    by
      calc Q * ((g : GL ι ℂ) : Matrix ι ι ℂ) * P * (Q * (((g : GL ι ℂ)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) * P)
          = Q * (((g : GL ι ℂ) : Matrix ι ι ℂ) * (P * Q) *
              (((g : GL ι ℂ)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ)) * P := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hPQ, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one,
              Matrix.mul_one, hQP],
    by
      calc Q * (((g : GL ι ℂ)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) * P * (Q * ((g : GL ι ℂ) : Matrix ι ι ℂ) * P)
          = Q * ((((g : GL ι ℂ)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) * (P * Q) *
              ((g : GL ι ℂ) : Matrix ι ι ℂ)) * P := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hPQ, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one,
              Matrix.mul_one, hQP]⟩,
    by
      rw [mem_unitaryGroupMatrix_star_iff]
      have hg := mem_unitaryGroupMatrix_star_iff.1 g.2
      have hPQh : Qᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, hPQ, conjTranspose_one]
      change (Q * ((g : GL ι ℂ) : Matrix ι ι ℂ) * P)ᴴ * H' * (Q * ((g : GL ι ℂ) : Matrix ι ι ℂ) * P) = H'
      set m := ((g : GL ι ℂ) : Matrix ι ι ℂ)
      rw [← hH']
      calc (Q * m * P)ᴴ * (Pᴴ * H * P) * (Q * m * P)
          = Pᴴ * mᴴ * (Qᴴ * Pᴴ) * H * (P * Q) * m * P := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = Pᴴ * H * P := by
            rw [hPQh, hPQ, Matrix.mul_one, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc H m P, ← Matrix.mul_assoc mᴴ (H * m) P, ← Matrix.mul_assoc mᴴ H m,
              hg]⟩
theorem coe_congrUnitary (hQP : Q * P = 1) (hPQ : P * Q = 1) (hH' : Pᴴ * H * P = H')
    (g : unitaryGroupMatrix (starRingEnd ℂ) H) :
    ((congrUnitary hQP hPQ hH' g : GL κ ℂ) : Matrix κ κ ℂ) = Q * ((g : GL ι ℂ) : Matrix ι ι ℂ) * P :=
  rfl
theorem continuous_congrUnitary (hQP : Q * P = 1) (hPQ : P * Q = 1) (hH' : Pᴴ * H * P = H') :
    Continuous (congrUnitary hQP hPQ hH') := by
  have h1 : Continuous fun x : unitaryGroupMatrix (starRingEnd ℂ) H =>
      Q * ((x : GL ι ℂ) : Matrix ι ι ℂ) * P :=
    (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul
      continuous_const
  have h2 : Continuous fun x : unitaryGroupMatrix (starRingEnd ℂ) H =>
      Q * (((x : GL ι ℂ)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) * P :=
    (continuous_const.matrix_mul (Units.continuous_coe_inv.comp continuous_subtype_val)).matrix_mul
      continuous_const
  exact Continuous.subtype_mk (Units.continuous_iff.2 ⟨h1, h2⟩) _
def congrUnitaryEquiv (hQP : Q * P = 1) (hPQ : P * Q = 1) (hH' : Pᴴ * H * P = H') :
    unitaryGroupMatrix (starRingEnd ℂ) H ≃ₜ* unitaryGroupMatrix (starRingEnd ℂ) H' :=
  have hH : Qᴴ * H' * Q = H := by
    rw [← hH']
    calc Qᴴ * (Pᴴ * H * P) * Q = (P * Q)ᴴ * H * (P * Q) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = H := by rw [hPQ, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  { toFun := congrUnitary hQP hPQ hH'
    invFun := congrUnitary hPQ hQP hH
    left_inv := fun g => by
      apply Subtype.ext; apply Units.ext
      rw [coe_congrUnitary, coe_congrUnitary]
      simp only [← Matrix.mul_assoc]
      rw [hPQ, Matrix.one_mul, Matrix.mul_assoc, hPQ, Matrix.mul_one]
    right_inv := fun g => by
      apply Subtype.ext; apply Units.ext
      rw [coe_congrUnitary, coe_congrUnitary]
      simp only [← Matrix.mul_assoc]
      rw [hQP, Matrix.one_mul, Matrix.mul_assoc, hQP, Matrix.mul_one]
    map_mul' := fun g h => by
      apply Subtype.ext; apply Units.ext
      rw [Subgroup.coe_mul, Units.val_mul, coe_congrUnitary, coe_congrUnitary, coe_congrUnitary,
        Subgroup.coe_mul, Units.val_mul]
      calc Q * (((g : GL ι ℂ) : Matrix ι ι ℂ) * ((h : GL ι ℂ) : Matrix ι ι ℂ)) * P
          = Q * ((g : GL ι ℂ) : Matrix ι ι ℂ) * (P * Q) * ((h : GL ι ℂ) : Matrix ι ι ℂ) * P := by
            rw [hPQ, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]
    continuous_toFun := continuous_congrUnitary hQP hPQ hH'
    continuous_invFun := continuous_congrUnitary hPQ hQP hH }
end Congr
theorem unitaryGroupMatrix_indefJ (p q : ℕ) :
    unitaryGroupMatrix (starRingEnd ℂ) (indefJ p q) = indefiniteUnitaryGroup p q := by
  ext g
  rw [mem_unitaryGroupMatrix_star_iff, mem_indefiniteUnitaryGroup_iff]
def subgroupCongrHomeomorph {n : Type*} [Fintype n] [DecidableEq n] {A B : Subgroup (GL n ℂ)}
    (h : A = B) : A ≃ₜ* B where
  toFun g := ⟨g.1, h ▸ g.2⟩
  invFun g := ⟨g.1, h ▸ g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _
section Equiv
variable (hH)
noncomputable def sylvesterP (hu : IsUnit H.det) :
    Matrix ι (Fin (posEigenCount hH) ⊕ Fin (negEigenCount hH)) ℂ :=
  (exists_congr_indefJ (hH := hH) hu).choose
noncomputable def sylvesterQ (hu : IsUnit H.det) :
    Matrix (Fin (posEigenCount hH) ⊕ Fin (negEigenCount hH)) ι ℂ :=
  (exists_congr_indefJ (hH := hH) hu).choose_spec.choose
variable {hH}
theorem sylvester_spec (hu : IsUnit H.det) :
    sylvesterQ hH hu * sylvesterP hH hu = 1 ∧ sylvesterP hH hu * sylvesterQ hH hu = 1 ∧
      (sylvesterP hH hu)ᴴ * H * sylvesterP hH hu =
        indefJ (posEigenCount hH) (negEigenCount hH) :=
  (exists_congr_indefJ (hH := hH) hu).choose_spec.choose_spec
noncomputable def unitaryHermitianEquiv (hu : IsUnit H.det) :
    unitaryGroupMatrix (starRingEnd ℂ) H ≃ₜ*
      indefiniteUnitaryGroup (posEigenCount hH) (negEigenCount hH) :=
  (congrUnitaryEquiv (sylvester_spec (hH := hH) hu).1 (sylvester_spec (hH := hH) hu).2.1
    (sylvester_spec (hH := hH) hu).2.2).trans (subgroupCongrHomeomorph (unitaryGroupMatrix_indefJ _ _))
end Equiv
end GroundTheory.Heights₂.Theta


