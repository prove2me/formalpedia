-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_GlRelOfBracket
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_GlRelOfBracket
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:23.515157+00:00
-- url     : https://prove2.me/theorems/fbf35e89-ecd6-47f4-8b28-eb86437882d5
-- title:
--   Gl Rel Of Bracket
-- statement:
--   Definitions and structural lemmas for Gl Rel Of Bracket, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/GlRelOfBracket.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply


set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
open PI.UpqRep (IsURepOn UJset inG)
open PI.DSInfCharCap (dsigC thetaJ)
open PI.PhMeasCore (dsig smoothVecs)
open Formalism.REAL (Jm)
noncomputable section
namespace GlobalTheory.CompanionTheory.SmoothModule
variable {n : ℕ} {ε : Fin n → Bool}
theorem J_mul_J (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext a; split_ifs <;> simp
theorem J_conj (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, diagonal_conjTranspose]
  congr 1; funext a; simp only [Pi.star_apply]; split_ifs <;> simp
theorem J_J_mul (X : Matrix (Fin n) (Fin n) ℂ) : Jm ε * (Jm ε * X) = X := by
  rw [← Matrix.mul_assoc, J_mul_J, Matrix.one_mul]
theorem inG_iff {X : Matrix (Fin n) (Fin n) ℂ} : inG ε X ↔ thetaJ ε X = X := by
  change Xᴴ * Jm ε + Jm ε * X = 0 ↔ _
  unfold thetaJ
  constructor
  · intro h
    rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left h, Matrix.mul_neg, neg_neg, J_J_mul]
  · intro h
    have : Jm ε * X = -(Xᴴ * Jm ε) := by
      conv_lhs => rw [← h]
      rw [Matrix.mul_neg, Matrix.mul_assoc, J_J_mul]
    rw [this, add_neg_cancel]
theorem theta_add (X Y : Matrix (Fin n) (Fin n) ℂ) : thetaJ ε (X + Y) = thetaJ ε X + thetaJ ε Y := by
  simp only [thetaJ, conjTranspose_add, Matrix.mul_add, Matrix.add_mul, neg_add]
theorem theta_sub (X Y : Matrix (Fin n) (Fin n) ℂ) : thetaJ ε (X - Y) = thetaJ ε X - thetaJ ε Y := by
  simp only [thetaJ, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]; abel
theorem theta_smul (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    thetaJ ε (c • X) = (starRingEnd ℂ c) • thetaJ ε X := by
  simp only [thetaJ, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]; rfl
theorem theta_theta (X : Matrix (Fin n) (Fin n) ℂ) : thetaJ ε (thetaJ ε X) = X := by
  simp only [thetaJ, conjTranspose_neg, conjTranspose_mul, J_conj, conjTranspose_conjTranspose,
    Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, J_J_mul, J_mul_J, Matrix.mul_one]
theorem inG_add {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y) : inG ε (X + Y) := by
  rw [inG_iff] at *; rw [theta_add, hX, hY]
theorem inG_smul (s : ℝ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) : inG ε ((s : ℂ) • X) := by
  rw [inG_iff] at *; rw [theta_smul, hX, Complex.conj_ofReal]
def re (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Y + thetaJ ε Y)
def im (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / (2 * Complex.I)) • (Y - thetaJ ε Y)
theorem inv_two_I : (1 / (2 * Complex.I) : ℂ) = -(1 / 2) * Complex.I := by
  have := Complex.I_ne_zero
  field_simp
  simp
theorem inG_re (Y : Matrix (Fin n) (Fin n) ℂ) : inG ε (re ε Y) := by
  rw [inG_iff, re, theta_smul, theta_add, theta_theta, add_comm]
  congr 1
  simp [Complex.conj_ofNat]
theorem inG_im (Y : Matrix (Fin n) (Fin n) ℂ) : inG ε (im ε Y) := by
  rw [inG_iff, im, theta_smul, theta_sub, theta_theta, ← neg_sub Y, smul_neg, ← neg_smul, inv_two_I]
  congr 1
  simp [Complex.conj_ofNat]
theorem re_add_im (Y : Matrix (Fin n) (Fin n) ℂ) : re ε Y + Complex.I • im ε Y = Y := by
  rw [re, im, inv_two_I, smul_smul]
  have : Complex.I * (-(1 / 2) * Complex.I) = 1 / 2 := by
    linear_combination (-(1 / 2) : ℂ) * Complex.I_mul_I
  rw [this]; module
theorem theta_pair {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inG ε A) (hB : inG ε B) :
    thetaJ ε (A + Complex.I • B) = A - Complex.I • B := by
  rw [theta_add, theta_smul, inG_iff.1 hA, inG_iff.1 hB, Complex.conj_I, neg_smul, sub_eq_add_neg]
theorem re_pair {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inG ε A) (hB : inG ε B) :
    re ε (A + Complex.I • B) = A := by
  rw [re, theta_pair hA hB]; module
theorem im_pair {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inG ε A) (hB : inG ε B) :
    im ε (A + Complex.I • B) = B := by
  rw [im, theta_pair hA hB, inv_two_I]
  have h : A + Complex.I • B - (A - Complex.I • B) = (2 * Complex.I) • B := by module
  have : (-(1 / 2) * Complex.I) * (2 * Complex.I) = 1 := by
    linear_combination (-1 : ℂ) * Complex.I_mul_I
  rw [h, smul_smul, this, one_smul]
def cext {M : Type*} [AddCommGroup M] [Module ℂ M] (ε : Fin n → Bool) (d : Matrix (Fin n) (Fin n) ℂ → M)
    (hadd : ∀ X Y, inG ε X → inG ε Y → d (X + Y) = d X + d Y)
    (hsmul : ∀ (s : ℝ) X, inG ε X → d ((s : ℂ) • X) = (s : ℂ) • d X) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M where
  toFun Y := d (re ε Y) + Complex.I • d (im ε Y)
  map_add' Y Z := by
    have h1 : re ε (Y + Z) = re ε Y + re ε Z := by simp only [re, theta_add]; module
    have h2 : im ε (Y + Z) = im ε Y + im ε Z := by simp only [im, theta_add]; module
    rw [h1, h2, hadd _ _ (inG_re _) (inG_re _), hadd _ _ (inG_im _) (inG_im _)]
    module
  map_smul' c Y := by
    have hA := inG_re (ε := ε) Y
    have hB := inG_im (ε := ε) Y
    have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
    have hI : ∀ {N : Type _} [AddCommGroup N] [Module ℂ N] (a b : N), c • (a + Complex.I • b) =
        ((c.re : ℂ) • a + ((-c.im : ℝ) : ℂ) • b) + Complex.I • ((c.im : ℂ) • a + (c.re : ℂ) • b) := by
      intro N _ _ a b
      conv_lhs => rw [hc]
      push_cast
      match_scalars
      · ring
      · linear_combination (c.im : ℂ) * Complex.I_mul_I
    have h : c • Y = ((c.re : ℂ) • re ε Y + ((-c.im : ℝ) : ℂ) • im ε Y) +
        Complex.I • ((c.im : ℂ) • re ε Y + (c.re : ℂ) • im ε Y) := by
      conv_lhs => rw [← re_add_im (ε := ε) Y, hc]
      push_cast
      match_scalars
      · ring
      · linear_combination (c.im : ℂ) * Complex.I_mul_I
    have h1 := inG_add (inG_smul c.re hA) (inG_smul (-c.im) hB)
    have h2 := inG_add (inG_smul c.im hA) (inG_smul c.re hB)
    rw [h, re_pair h1 h2, im_pair h1 h2, hadd _ _ (inG_smul _ hA) (inG_smul _ hB),
      hadd _ _ (inG_smul _ hA) (inG_smul _ hB), hsmul _ _ hA, hsmul _ _ hA, hsmul _ _ hB, hsmul _ _ hB,
      RingHom.id_apply, hI]
section Analytic
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
end Analytic
end GlobalTheory.CompanionTheory.SmoothModule


