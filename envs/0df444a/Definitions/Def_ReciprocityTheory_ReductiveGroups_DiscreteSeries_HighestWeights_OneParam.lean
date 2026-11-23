-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:01:12.168337+00:00
-- url     : https://prove2.me/theorems/593ae313-b11c-4dc7-b74e-62685933c952
-- title:
--   One Param
-- statement:
--   Definitions and structural lemmas for One Param, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/OneParam.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
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
namespace ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
lemma onep_skew {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) : Xᴴ = -X := by
  unfold inK inG at hX
  obtain ⟨h1, h2⟩ := hX
  have hJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have h3 : Xᴴ * Jm ε = -(X * Jm ε) := by
    rw [h2]
    exact eq_neg_of_add_eq_zero_left h1
  calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, hJ, mul_one]
    _ = -(X * Jm ε) * Jm ε := by rw [h3]
    _ = -X := by rw [neg_mul, mul_assoc, hJ, mul_one]
lemma onep_exp_conjT {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • X))ᴴ = NormedSpace.exp (-((t : ℂ) • X)) := by
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, onep_skew hX]
  have hs : (star (t : ℂ)) = t := Complex.conj_ofReal t
  rw [hs, smul_neg]
lemma onep_exp_neg_mul (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl A).neg_left)]
  simp
lemma onep_exp_mul_neg (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp A * NormedSpace.exp (-A) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl A).neg_right)]
  simp
lemma onep_commJ {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    Commute (Jm ε) (NormedSpace.exp ((t : ℂ) • X)) := (Commute.smul_right (show Commute (Jm ε) X from (show inG ε X ∧ X * Jm ε = Jm ε * X from hX).2.symm)
    (t : ℂ)).exp_right
lemma onep_inUJ {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    inUJ ε (NormedSpace.exp ((t : ℂ) • X)) := by
  unfold inUJ
  rw [onep_exp_conjT hX t, mul_assoc, (onep_commJ hX t).eq, ← mul_assoc, onep_exp_neg_mul, one_mul]
lemma onep_Kset {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε := by
  unfold Kset
  simp only [Set.mem_setOf_eq]
  refine ⟨?_, (onep_commJ hX t).eq.symm⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, onep_exp_conjT hX t, onep_exp_mul_neg]
def onepCurve (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) : KG ε :=
  ⟨⟨(Matrix.isUnit_exp ((t : ℂ) • X)).unit, by
      show inUJ ε ((Matrix.isUnit_exp ((t : ℂ) • X)).unit : Matrix (Fin n) (Fin n) ℂ)
      rw [IsUnit.unit_spec]
      exact onep_inUJ hX t⟩, by
    show ((Matrix.isUnit_exp ((t : ℂ) • X)).unit : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε
    rw [IsUnit.unit_spec]
    exact onep_Kset hX t⟩
end ReciprocityTheory.ChartRestriction.DS.HW


