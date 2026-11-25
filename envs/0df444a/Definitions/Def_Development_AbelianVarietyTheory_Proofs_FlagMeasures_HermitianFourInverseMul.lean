-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:28:54.962506+00:00
-- url     : https://prove2.me/theorems/5851532a-899b-5fbf-8637-6d7fefa901b8
-- title:
--   Hermitian Four Inverse Mul
-- statement:
--   Definitions and structural lemmas for Hermitian Four Inverse Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFourInverseMul.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Model_hf_add_left
import Theorems.Thm_GlobalTheory_HL_Model_hf_smul_left
import Theorems.Thm_GlobalTheory_HL_Model_nontrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
section General
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
def proj (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) : S.V →ₗ[E] S.V where
  toFun v := v - ∑ j, hf L S.Hm v (gs j) • g j.castSucc - ∑ j, hf L S.Hm v (g j.castSucc) • gs j
  map_add' a b := by
    simp only [hf_add_left, add_smul, Finset.sum_add_distrib]; abel
  map_smul' c a := by
    simp only [hf_smul_left, mul_smul, RingHom.id_apply, smul_sub, Finset.smul_sum]
def innerOf (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (Λ : Submodule L.O S.V) : Submodule L.O S.V :=
  (perp L S.Hm (S.spanTo g r)).restrictScalars L.O ⊓ Λ.comap ((proj S g gs).restrictScalars L.O)
end General
section Blocks
variable {s m N : ℕ} (e : Fin s ⊕ Fin m ≃ Fin N)
def extZ (x : Fin s → E) : Fin N → E := Sum.elim x 0 ∘ e.symm
def big (H : Matrix (Fin s) (Fin s) E) : Matrix (Fin N) (Fin N) E :=
  Matrix.reindex e e (Matrix.fromBlocks H 0 0 (1 : Matrix (Fin m) (Fin m) E))
theorem hf_extZ (L : LocE F E) (H : Matrix (Fin s) (Fin s) E) (x y : Fin s → E) :
    hf L (big e H) (extZ e x) (extZ e y) = hf L H x y := by
  have key : ∀ f : Fin N → E, ∑ i, f i = ∑ p, f (e p) := fun f => (e.sum_comp f).symm
  simp only [hf, key, Fintype.sum_sum_type, extZ, big, Matrix.reindex_apply, Matrix.submatrix_apply,
    Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
    Matrix.fromBlocks_apply₁₁, zero_mul, map_zero, mul_zero, Finset.sum_const_zero, add_zero]
theorem big_mul (H K : Matrix (Fin s) (Fin s) E) (h : K * H = 1) : big e K * big e H = 1 := by
  simp [big, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, h,
    Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
theorem big_herm (L : LocE F E) (H K : Matrix (Fin s) (Fin s) E) (hH : ∀ a b, L.cj (H b a) = H a b)
    (h : K * H = 1) : IsHermND L (big e H) := by
  refine ⟨?_, Matrix.isUnit_det_of_left_inverse (big_mul e H K h)⟩
  unfold IsHerm
  ext a b
  obtain ⟨p, rfl⟩ := e.surjective a
  obtain ⟨q, rfl⟩ := e.surjective b
  simp only [cT, big, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases p with p | p <;> rcases q with q | q
  · simpa using hH p q
  · simp
  · simp
  · by_cases hpq : p = q
    · subst hpq
      simp
    · simp [Matrix.one_apply_ne hpq, Matrix.one_apply_ne (Ne.symm hpq)]
end Blocks
def e4 (m : ℕ) : Fin 4 ⊕ Fin m ≃ Fin (m + 1 + 2 * 1 + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))
def H4 : Matrix (Fin 4) (Fin 4) E := !![0,0,0,1; 0,-1,-1,0; 0,-1,0,0; 1,0,0,-1]
def K4 : Matrix (Fin 4) (Fin 4) E := !![1,0,0,1; 0,0,-1,0; 0,-1,1,0; 1,0,0,0]
theorem hermitian_four_inverse_mul : (K4 : Matrix (Fin 4) (Fin 4) E) * H4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [K4, H4, Matrix.mul_apply, Fin.sum_univ_succ]
def toyExample (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) : Frames L 1 (m + 1) where
  ϖ := ϖ
  ϖ_irr := hϖ
  Hm := big (e4 m) H4
  herm := big_herm _ L _ K4 (by intro a b; fin_cases a <;> fin_cases b <;> simp [H4]) hermitian_four_inverse_mul
  T := 1
  T' := 1
  f := ![extZ (e4 m) ![1,0,0,0], extZ (e4 m) ![0,1,0,0]]
  f' := ![extZ (e4 m) ![0,0,1,0], extZ (e4 m) ![0,0,0,1]]
  es := ![extZ (e4 m) ![0,1,-1,1]]
  es' := ![extZ (e4 m) ![1,-1,0,1]]
  gram := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ] <;> simp [H4, hf, Fin.sum_univ_succ, Fin.last]
  gram' := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ] <;> simp [H4, hf, Fin.sum_univ_succ, Fin.last]
  dual := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ] <;> simp [H4, hf, Fin.sum_univ_succ]
  dual' := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ] <;> simp [H4, hf, Fin.sum_univ_succ]
  iso := by
    intro a b; fin_cases a; fin_cases b; simp [hf_extZ]; simp [H4, hf, Fin.sum_univ_succ]
  iso' := by
    intro a b; fin_cases a; fin_cases b; simp [hf_extZ]; simp [H4, hf, Fin.sum_univ_succ]
  w := ⟨[(1, 2)], rfl⟩
  relevant := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [hf_extZ] <;> simp [H4, hf, Fin.sum_univ_succ, Pt.mat, ptEntryL]
  G_ne := by
    haveI := nontrivial L
    simp [lead, Matrix.det_succ_row_zero, hf_extZ, Fin.sum_univ_succ, Fin.last, Fin.castLE, Fin.succAbove]
    simp [H4, hf, Fin.sum_univ_succ]
  gg := false
  gg_ok := by simp
def e6 (m : ℕ) : Fin 6 ⊕ Fin m ≃ Fin (m + 3 + 2 * 1 + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))
def H6 : Matrix (Fin 6) (Fin 6) E :=
  !![0,1,0,0,0,0; 1,0,0,0,0,0; 0,0,0,1,0,0; 0,0,1,0,0,0; 0,0,0,0,-1,0; 0,0,0,0,0,1]
theorem hermitian_six_mul_self : (H6 : Matrix (Fin 6) (Fin 6) E) * H6 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H6, Matrix.mul_apply, Fin.sum_univ_succ]
theorem hermitian_form_six_apply (L : LocE F E) (x y : Fin 6 → E) : hf L H6 x y =
    x 0 * L.cj (y 1) + x 1 * L.cj (y 0) + x 2 * L.cj (y 3) + x 3 * L.cj (y 2) - x 4 * L.cj (y 4) +
      x 5 * L.cj (y 5) := by
  simp [hf, Fin.sum_univ_succ, H6]
  ring
theorem isUnit_one_sub_sq (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) : IsUnit (1 - ϖ ^ 2) := by
  have hv := Valuation.integer.integers (valuation F)
  have h1 : valuation F (ϖ : F) < 1 := by
    have hne : valuation F (algebraMap 𝒪[F] F ϖ) ≠ 1 := fun h =>
      hϖ.not_isUnit (hv.isUnit_iff_valuation_eq_one.2 h)
    exact lt_of_le_of_ne ((Valuation.mem_integer_iff _ _).1 ϖ.2) hne
  rw [hv.isUnit_iff_valuation_eq_one]
  have h2 : valuation F ((ϖ : F) ^ 2) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le h1 (by norm_num)
  have h3 : algebraMap 𝒪[F] F (1 - ϖ ^ 2) = 1 - (ϖ : F) ^ 2 := by
    rw [map_sub, map_one, map_pow]
    rfl
  rw [h3]
  exact Valuation.map_one_sub_of_lt _ h2
theorem coe_ne_zero (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) : (ϖ : F) ≠ 0 := by
  intro h
  exact hϖ.ne_zero (Subtype.ext h)
def toyG (L : LocE F E) (hE : ¬ IsField E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) :
    Frames L 1 (m + 3) where
  ϖ := ϖ
  ϖ_irr := hϖ
  Hm := big (e6 m) H6
  herm := big_herm _ L _ H6 (by intro a b; fin_cases a <;> fin_cases b <;> simp [H6]) hermitian_six_mul_self
  T := 1
  T' := Units.map (𝒪[F]).subtype.toMonoidHom (isUnit_one_sub_sq ϖ hϖ).unit
  f := ![extZ (e6 m) ![1,0,0,0,0,0], extZ (e6 m) ![0,0,0,0,1,0]]
  f' := ![extZ (e6 m) ![1, -(algebraMap F E ϖ) ^ 2, algebraMap F E ϖ, algebraMap F E ϖ, 0, 0],
    extZ (e6 m) ![0,0,0,0,1,algebraMap F E ϖ]]
  es := ![extZ (e6 m) ![0,1,0,0,0,0]]
  es' := ![extZ (e6 m) ![0,1,0,0,0,0]]
  gram := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ, hermitian_form_six_apply, Fin.last]
  gram' := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ, hermitian_form_six_apply, Fin.last] <;> ring
  dual := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ, hermitian_form_six_apply]
  dual' := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ, hermitian_form_six_apply]
  iso := by
    intro a b; fin_cases a; fin_cases b; simp [hf_extZ, hermitian_form_six_apply]
  iso' := by
    intro a b; fin_cases a; fin_cases b; simp [hf_extZ, hermitian_form_six_apply]
  w := ⟨[(Units.map (algebraMap F E).toMonoidHom (Units.mk0 (ϖ : F) (coe_ne_zero ϖ hϖ)) ^ 2, 1), (-1, 1)], rfl⟩
  relevant := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [hf_extZ, hermitian_form_six_apply, Pt.mat, ptEntryL]
  G_ne := by
    haveI := nontrivial L
    have h6 : (algebraMap F E ϖ) ^ 6 ≠ 0 := by
      rw [← map_pow]
      exact (map_ne_zero _).2 (pow_ne_zero _ (coe_ne_zero ϖ hϖ))
    convert h6 using 1
    simp [lead, Matrix.det_succ_row_zero, hf_extZ, hermitian_form_six_apply, Fin.sum_univ_succ, Fin.last, Fin.castLE,
      Fin.succAbove]
    ring
  gg := true
  gg_ok := fun _ => ⟨hE, ⟨1, rfl⟩, ⟨(isUnit_one_sub_sq ϖ hϖ).unit, rfl⟩⟩
end GlobalTheory.HL.Inhab


