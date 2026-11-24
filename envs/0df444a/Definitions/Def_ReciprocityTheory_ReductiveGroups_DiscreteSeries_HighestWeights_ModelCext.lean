-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelCext
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelCext
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:34:30.369323+00:00
-- url     : https://prove2.me/theorems/58876a9b-3cc5-4b66-9cc5-3420e7646291
-- title:
--   Model Cext
-- statement:
--   Definitions and structural lemmas for Model Cext, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelCext.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
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
def bdPart (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if ε a = ε b then Z a b else 0
theorem cpart1_bdPart_apply (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    cpart1 ε (bdPart ε Z) a b = if ε a = ε b then (Z a b - star (Z b a)) / 2 else 0 := by
  by_cases ha : ε a <;> by_cases hb : ε b <;>
    simp [cpart1, bdPart, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, ha, hb] <;> ring
theorem cpart2_bdPart_apply (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    cpart2 ε (bdPart ε Z) a b = if ε a = ε b then -Complex.I * (Z a b + star (Z b a)) / 2 else 0 := by
  have hI : (1 / (2 * Complex.I)) = -Complex.I / 2 := by
    rw [one_div, mul_inv, Complex.inv_I]; ring
  by_cases ha : ε a <;> by_cases hb : ε b <;>
    simp [cpart2, hI, bdPart, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, ha, hb] <;> ring
theorem inK_cpart1_bdPart (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inK ε (cpart1 ε (bdPart ε Z)) := by
  refine ⟨?_, ?_⟩ <;> ext a b <;>
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply, Matrix.conjTranspose_apply,
      cpart1_bdPart_apply, Matrix.zero_apply] <;>
    by_cases ha : ε a <;> by_cases hb : ε b <;> simp [ha, hb] <;> ring
theorem inK_cpart2_bdPart (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inK ε (cpart2 ε (bdPart ε Z)) := by
  refine ⟨?_, ?_⟩ <;> ext a b <;>
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply, Matrix.conjTranspose_apply,
      cpart2_bdPart_apply, Matrix.zero_apply] <;>
    by_cases ha : ε a <;> by_cases hb : ε b <;> simp [ha, hb] <;> ring
theorem cpart1_bdPart_add (ε : Fin n → Bool) (Z Z' : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε (bdPart ε (Z + Z')) = cpart1 ε (bdPart ε Z) + cpart1 ε (bdPart ε Z') := by
  ext a b
  simp only [Matrix.add_apply, cpart1_bdPart_apply, star_add]
  split_ifs <;> ring
theorem cpart2_bdPart_add (ε : Fin n → Bool) (Z Z' : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε (bdPart ε (Z + Z')) = cpart2 ε (bdPart ε Z) + cpart2 ε (bdPart ε Z') := by
  ext a b
  simp only [Matrix.add_apply, cpart2_bdPart_apply, star_add]
  split_ifs <;> ring
theorem cpart1_bdPart_smul (ε : Fin n → Bool) (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε (bdPart ε (c • Z)) =
      ((c.re : ℝ) : ℂ) • cpart1 ε (bdPart ε Z) + ((-c.im : ℝ) : ℂ) • cpart2 ε (bdPart ε Z) := by
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, cpart1_bdPart_apply, cpart2_bdPart_apply, star_mul']
  split_ifs
  · apply Complex.ext <;> simp <;> ring
  · simp
theorem cpart2_bdPart_smul (ε : Fin n → Bool) (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε (bdPart ε (c • Z)) =
      ((c.im : ℝ) : ℂ) • cpart1 ε (bdPart ε Z) + ((c.re : ℝ) : ℂ) • cpart2 ε (bdPart ε Z) := by
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, cpart1_bdPart_apply, cpart2_bdPart_apply, star_mul']
  split_ifs
  · apply Complex.ext <;> simp <;> ring
  · simp
theorem inK_ofReal_smul (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (r : ℝ) :
    inK ε ((r : ℂ) • X) := by
  obtain ⟨h1, h2⟩ := hX
  have hr : star (r : ℂ) = r := by simp
  constructor
  · change ((r : ℂ) • X)ᴴ * Jm ε + Jm ε * ((r : ℂ) • X) = 0
    change Xᴴ * Jm ε + Jm ε * X = 0 at h1
    rw [conjTranspose_smul, hr, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]
  · rw [Matrix.smul_mul, Matrix.mul_smul, h2]
section Op
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
def RLinOnK (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) : Prop :=
  ∀ (X Y : Matrix (Fin n) (Fin n) ℂ) (r : ℝ), inK ε X → inK ε Y →
    A (X + Y) = A X + A Y ∧ A ((r : ℂ) • X) = (r : ℂ) • A X
def cext (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (Z : Matrix (Fin n) (Fin n) ℂ) :
    V →L[ℂ] V :=
  A (cpart1 ε (bdPart ε Z)) + Complex.I • A (cpart2 ε (bdPart ε Z))
theorem smul_combo (c : ℂ) (u v : V →L[ℂ] V) :
    ((c.re : ℝ) : ℂ) • u + ((-c.im : ℝ) : ℂ) • v + Complex.I • (((c.im : ℝ) : ℂ) • u + ((c.re : ℝ) : ℂ) • v) =
      c • (u + Complex.I • v) := by
  have hc : (c.re : ℂ) + c.im * Complex.I = c := Complex.re_add_im c
  push_cast
  linear_combination (norm := module) hc • (u + Complex.I • v) - ((c.im : ℂ) * Complex.I_sq) • v
theorem cext_add (ε : Fin n → Bool) {A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} (hA : RLinOnK ε A)
    (Z Z' : Matrix (Fin n) (Fin n) ℂ) : cext ε A (Z + Z') = cext ε A Z + cext ε A Z' := by
  unfold cext
  rw [cpart1_bdPart_add, cpart2_bdPart_add,
    (hA _ _ 0 (inK_cpart1_bdPart ε Z) (inK_cpart1_bdPart ε Z')).1,
    (hA _ _ 0 (inK_cpart2_bdPart ε Z) (inK_cpart2_bdPart ε Z')).1, smul_add]
  abel
theorem cext_smul (ε : Fin n → Bool) {A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} (hA : RLinOnK ε A)
    (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) : cext ε A (c • Z) = c • cext ε A Z := by
  have hP := inK_cpart1_bdPart ε Z
  have hQ := inK_cpart2_bdPart ε Z
  unfold cext
  rw [cpart1_bdPart_smul, cpart2_bdPart_smul,
    (hA _ _ 0 (inK_ofReal_smul ε hP _) (inK_ofReal_smul ε hQ _)).1,
    (hA _ _ 0 (inK_ofReal_smul ε hP _) (inK_ofReal_smul ε hQ _)).1,
    (hA _ _ c.re hP hP).2, (hA _ _ (-c.im) hQ hQ).2, (hA _ _ c.im hP hP).2, (hA _ _ c.re hQ hQ).2]
  exact smul_combo c _ _
def cextL (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (hA : RLinOnK ε A) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V) where
  toFun := cext ε A
  map_add' := cext_add ε hA
  map_smul' := cext_smul ε hA
end Op
end ReciprocityTheory.ChartRestriction.DS.HW


