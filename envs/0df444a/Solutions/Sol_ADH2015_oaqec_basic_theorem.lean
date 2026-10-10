-- Prove2me | solution 1 for ADH2015.oaqec_basic_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-09T14:45:22.250327+00:00
-- url     : https://prove2.me/submissions/b88890c2-cf0d-45cb-af85-4eda1210015d

import Mathlib
import Definitions.Def_ADH2015_defs
import Theorems.Thm_QInfo_commute_mul_conjTranspose_iff_exists_mirror
import Theorems.Thm_QInfo_exists_orthogonalProjector

open Matrix ADH2015
open scoped Kronecker

theorem solution {e ē : Type*} [Fintype e] [Fintype ē] [DecidableEq e]
    [DecidableEq ē] (C : Submodule ℂ (e × ē → ℂ)) (O : Matrix (e × ē) (e × ē) ℂ)
    (hO : ActsWithin C O) :
    HasRepOnBar C O ↔
      ∀ X : Matrix e e ℂ, ∀ v ∈ C, ∀ w ∈ C,
        star w ⬝ᵥ ((O * (X ⊗ₖ (1 : Matrix ē ē ℂ)) - (X ⊗ₖ (1 : Matrix ē ē ℂ)) * O) *ᵥ v) = 0 := by
  have hK : ∀ (X : Matrix e e ℂ) (Y : Matrix ē ē ℂ),
      ((1 : Matrix e e ℂ) ⊗ₖ Y) * (X ⊗ₖ (1 : Matrix ē ē ℂ)) =
        (X ⊗ₖ (1 : Matrix ē ē ℂ)) * ((1 : Matrix e e ℂ) ⊗ₖ Y) := by
    intro X Y; rw [← mul_kronecker_mul, ← mul_kronecker_mul]; simp
  constructor
  · -- (3.27) ⇒ (3.28): `O` may be replaced by `𝟙_E ⊗ Y` on both sides of the matrix element.
    rintro ⟨Y, hY⟩ X v hv w hw
    have hrow : star w ᵥ* O = star w ᵥ* ((1 : Matrix e e ℂ) ⊗ₖ Y) := by
      calc star w ᵥ* O = star (Oᴴ *ᵥ w) := by rw [star_mulVec, conjTranspose_conjTranspose]
        _ = star (((1 : Matrix e e ℂ) ⊗ₖ Y)ᴴ *ᵥ w) := by rw [(hY w hw).2]
        _ = star w ᵥ* ((1 : Matrix e e ℂ) ⊗ₖ Y) := by
          rw [star_mulVec, conjTranspose_conjTranspose]
    rw [sub_mulVec, dotProduct_sub, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, hrow,
      ← dotProduct_mulVec, ← (hY v hv).1, mulVec_mulVec, mulVec_mulVec, hK, sub_self]
  · -- (3.28) ⇒ (3.27): Appendix B, via the reference system `R` and the mirror lemma.
    intro hcomm
    obtain ⟨P, hPH, hPP, hPC, hPfix⟩ := QInfo.exists_orthogonalProjector C
    have hext : ∀ M N : Matrix (e × ē) (e × ē) ℂ, (∀ u, M *ᵥ u = N *ᵥ u) → M = N :=
      fun M N h => ext_of_mulVec_single fun i => h _
    -- `O` and `O†` preserve the code subspace, so `O` commutes with the projector `P`.
    have hOP1 : P * (O * P) = O * P := hext _ _ fun u => by
      simp only [← mulVec_mulVec]; exact hPfix _ (hO _ (hPC u)).1
    have hOP2 : P * (Oᴴ * P) = Oᴴ * P := hext _ _ fun u => by
      simp only [← mulVec_mulVec]; exact hPfix _ (hO _ (hPC u)).2
    have hPO : P * O = O * P := by
      have h := congrArg conjTranspose hOP2
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, hPH.eq] at h
      rw [← h, Matrix.mul_assoc, hOP1]
    -- (B.13): the commutator condition, as a matrix identity sandwiched between projectors.
    have hPMP : ∀ X : Matrix e e ℂ,
        P * (O * (X ⊗ₖ (1 : Matrix ē ē ℂ)) - (X ⊗ₖ (1 : Matrix ē ē ℂ)) * O) * P = 0 := by
      intro X; ext y x
      have h := hcomm X _ (hPC (Pi.single x 1)) _ (hPC (Pi.single y 1))
      rw [mulVec_single_one, mulVec_single_one] at h
      rw [Matrix.zero_apply, ← h, Matrix.mul_assoc]
      nth_rw 1 [← hPH.eq]
      rfl
    have key : ∀ X : Matrix e e ℂ,
        P * (X ⊗ₖ (1 : Matrix ē ē ℂ)) * (O * P) = O * P * (X ⊗ₖ (1 : Matrix ē ē ℂ)) * P := by
      intro X
      have h := hPMP X
      rw [Matrix.mul_sub, Matrix.sub_mul, sub_eq_zero] at h
      calc P * (X ⊗ₖ (1 : Matrix ē ē ℂ)) * (O * P)
            = P * ((X ⊗ₖ (1 : Matrix ē ē ℂ)) * O) * P := by simp only [Matrix.mul_assoc]
        _ = P * (O * (X ⊗ₖ (1 : Matrix ē ē ℂ))) * P := h.symm
        _ = P * O * (X ⊗ₖ (1 : Matrix ē ē ℂ)) * P := by simp only [Matrix.mul_assoc]
        _ = O * P * (X ⊗ₖ (1 : Matrix ē ē ℂ)) * P := by rw [hPO]
    -- (B.11): the purification `|φ⟩ = ∑ₓ |x⟩_R ⊗ P|x⟩` on `R ⊗ E ⊗ Ē` (with `R ≅ E ⊗ Ē`), viewed
    -- as a matrix `W` from `Ē` to `R ⊗ E`; then `W W† = ρ_{RE}` and `O_R = (O P)ᵀ` (B.9).
    let W : Matrix ((e × ē) × e) ē ℂ := Matrix.of fun p b => P (p.2, b) p.1
    let A : Matrix ((e × ē) × e) ((e × ē) × e) ℂ := (O * P)ᵀ ⊗ₖ (1 : Matrix e e ℂ)
    have hWW : ∀ x a y a', (W * Wᴴ) (x, a) (y, a') =
        (P * (Matrix.single a' a (1 : ℂ) ⊗ₖ (1 : Matrix ē ē ℂ)) * P) y x := by
      intro x a y a'
      simp only [W, Matrix.mul_apply, conjTranspose_apply, of_apply, Fintype.sum_prod_type,
        kronecker_apply, one_apply, single_apply, hPH.apply, ite_mul, one_mul, zero_mul, mul_ite,
        mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_and]
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_one]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    -- (B.14): `[O_R ⊗ 𝟙_E, ρ_{RE}] = 0`.
    have hAcomm : A * (W * Wᴴ) = (W * Wᴴ) * A := by
      ext ⟨x, a⟩ ⟨y, a'⟩
      set S := Matrix.single a' a (1 : ℂ) ⊗ₖ (1 : Matrix ē ē ℂ) with hS
      have hM : P * S * P * (O * P) = O * P * (P * S * P) :=
        calc P * S * P * (O * P) = P * S * (P * (O * P)) := by simp only [Matrix.mul_assoc]
          _ = P * S * (O * P) := by rw [hOP1]
          _ = O * P * S * P := key _
          _ = O * (P * P) * S * P := by rw [hPP]
          _ = O * P * (P * S * P) := by simp only [Matrix.mul_assoc]
      rw [Matrix.mul_apply, Matrix.mul_apply]
      simp only [A, Fintype.sum_prod_type, kronecker_apply, transpose_apply, one_apply, mul_ite,
        ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, hWW, ← hS]
      calc _ = (P * S * P * (O * P)) y x := by
            rw [Matrix.mul_apply, Fintype.sum_prod_type]
            exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
        _ = (O * P * (P * S * P)) y x := by rw [hM]
        _ = _ := by
            rw [Matrix.mul_apply, Fintype.sum_prod_type]
            exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
    obtain ⟨B, hB1, hB2⟩ := (QInfo.commute_mul_conjTranspose_iff_exists_mirror W A).mp hAcomm
    -- Mirror `O_R` back onto `Ē` (B.15)–(B.17): `O_Ē = 𝟙_E ⊗ Bᵀ`.
    have transfer : ∀ Q' B' : Matrix _ _ ℂ, (Q'ᵀ ⊗ₖ (1 : Matrix e e ℂ)) * W = W * B' →
        ((1 : Matrix e e ℂ) ⊗ₖ B'ᵀ) * P = P * Q' := by
      intro Q' B' h
      ext ⟨a, b⟩ x
      have := congrFun (congrFun h (x, a)) b
      simp only [W, Matrix.mul_apply, of_apply, kronecker_apply, transpose_apply, one_apply,
        Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at this ⊢
      simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true] at this
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [show (∑ x_1, ∑ y, P (a, b) (x_1, y) * Q' (x_1, y) x) = _ from
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _, this]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have hY1 : ((1 : Matrix e e ℂ) ⊗ₖ Bᵀ) * P = O * P := by
      rw [transfer _ _ hB1, ← Matrix.mul_assoc, hPO, Matrix.mul_assoc, hPP]
    have hY2 : ((1 : Matrix e e ℂ) ⊗ₖ Bᵀ)ᴴ * P = Oᴴ * P := by
      have hA : Aᴴ = (O * P)ᴴᵀ ⊗ₖ (1 : Matrix e e ℂ) := by
        simp only [A, conjTranspose_kronecker, conjTranspose_one]; rfl
      rw [hA] at hB2
      rw [conjTranspose_kronecker, conjTranspose_one, show Bᵀᴴ = Bᴴᵀ from rfl,
        transfer _ _ hB2, conjTranspose_mul, hPH.eq, ← Matrix.mul_assoc, hPP]
      have h := congrArg conjTranspose hPO
      rw [conjTranspose_mul, conjTranspose_mul, hPH.eq] at h
      exact h.symm
    refine ⟨Bᵀ, fun v hv => ⟨?_, ?_⟩⟩
    · rw [← hPfix v hv, mulVec_mulVec, mulVec_mulVec, hY1]
    · rw [← hPfix v hv, mulVec_mulVec, mulVec_mulVec, hY2]
