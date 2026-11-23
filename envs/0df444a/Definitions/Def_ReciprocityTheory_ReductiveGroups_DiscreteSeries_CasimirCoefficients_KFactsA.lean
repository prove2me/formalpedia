-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFactsA
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFactsA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:04:45.901619+00:00
-- url     : https://prove2.me/theorems/575f9c58-d27b-4955-9685-fe6cebf35d3a
-- title:
--   KFacts A
-- statement:
--   Definitions and structural lemmas for KFacts A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/KFactsA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
lemma kfa_mul_Jm_apply (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Y * Jm ε) a b = Y a b * (if ε b then 1 else -1) := by
  unfold Jm
  rw [Matrix.mul_diagonal]
lemma kfa_Jm_mul_apply (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Jm ε * Y) a b = (if ε a then 1 else -1) * Y a b := by
  unfold Jm
  rw [Matrix.diagonal_mul]
lemma kfa_comm_iff_block (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    Y * Jm ε = Jm ε * Y ↔ IsBlock ε Y := by
  constructor
  · intro h a b hab
    have h1 := congrFun (congrFun h a) b
    rw [kfa_mul_Jm_apply, kfa_Jm_mul_apply] at h1
    rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
      rcases Bool.eq_false_or_eq_true (ε b) with hb | hb <;>
      simp [ha, hb] at h1 hab <;>
      first
      | exact h1
      | linear_combination h1
      | linear_combination (-1 / 2 : ℂ) * h1
      | linear_combination (1 / 2 : ℂ) * h1
  · intro h
    ext a b
    rw [kfa_mul_Jm_apply, kfa_Jm_mul_apply]
    by_cases hab : ε a = ε b
    · rw [hab]
      ring
    · rw [h a b hab]
      ring
lemma kfa_inK_iff (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    inK ε Y ↔ Yᴴ = -Y ∧ IsBlock ε Y := by
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  unfold inK inG
  rw [← kfa_comm_iff_block]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have h3 : (Yᴴ + Y) * Jm ε = 0 := by
      rw [Matrix.add_mul, h2]
      exact h1
    have h4 := congrArg (· * Jm ε) h3
    simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one, Matrix.zero_mul] at h4
    exact eq_neg_of_add_eq_zero_left h4
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h1, Matrix.neg_mul, h2, neg_add_cancel]
section ExpL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
lemma kfa_exp_comm {J X : Matrix (Fin n) (Fin n) ℂ} (h : X * J = J * X) :
    NormedSpace.exp X * J = J * NormedSpace.exp X := Commute.exp_left h
end ExpL
lemma kfa_exp_neg_mul (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl A).neg_left, neg_add_cancel, NormedSpace.exp_zero]
lemma kfa_exp_mul_neg (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp A * NormedSpace.exp (-A) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl A).neg_right, add_neg_cancel, NormedSpace.exp_zero]
lemma kfa_exp_conjTranspose {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Yᴴ = -Y) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • Y))ᴴ = NormedSpace.exp (-((t : ℂ) • Y)) := by
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hY, smul_neg]
  simp only [Complex.star_def, Complex.conj_ofReal]
def kfaUnit (Y : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  ⟨NormedSpace.exp ((t : ℂ) • Y), NormedSpace.exp (-((t : ℂ) • Y)), kfa_exp_mul_neg _, kfa_exp_neg_mul _⟩
lemma kfa_mem_Kset (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Y) ∈ Kset ε := by
  have hYJ : Y * Jm ε = Jm ε * Y := hY.2
  have hsk : Yᴴ = -Y := ((kfa_inK_iff ε Y).1 hY).1
  unfold Kset
  rw [Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, kfa_exp_conjTranspose hsk,
      kfa_exp_mul_neg]
  · exact kfa_exp_comm (by rw [Matrix.smul_mul, Matrix.mul_smul, hYJ])
lemma kfa_inUJ (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) :
    inUJ ε (NormedSpace.exp ((t : ℂ) • Y)) := by
  have hYJ : Y * Jm ε = Jm ε * Y := hY.2
  have hsk : Yᴴ = -Y := ((kfa_inK_iff ε Y).1 hY).1
  have hc : NormedSpace.exp ((t : ℂ) • Y) * Jm ε = Jm ε * NormedSpace.exp ((t : ℂ) • Y) :=
    kfa_exp_comm (by rw [Matrix.smul_mul, Matrix.mul_smul, hYJ])
  unfold inUJ
  rw [kfa_exp_conjTranspose hsk, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, kfa_exp_neg_mul,
    Matrix.one_mul]
def kfaUJ (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) : UJ ε :=
  ⟨kfaUnit Y t, kfa_inUJ ε hY t⟩
def kfaKG (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) : KG ε :=
  ⟨kfaUJ ε hY t, kfa_mem_Kset ε hY t⟩
end ReciprocityTheory.ChartRestriction.DS.S7


