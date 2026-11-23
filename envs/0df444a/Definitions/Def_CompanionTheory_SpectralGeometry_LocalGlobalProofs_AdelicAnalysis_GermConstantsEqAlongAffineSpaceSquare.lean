-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GermConstantsEqAlongAffineSpaceSquare
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GermConstantsEqAlongAffineSpaceSquare
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:53.774119+00:00
-- url     : https://prove2.me/theorems/b59ce67d-e75b-419d-88cd-79bae1412be6
-- title:
--   Germ Constants Eq Along Affine Space Square
-- statement:
--   Definitions and structural lemmas for Germ Constants Eq Along Affine Space Square, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GermConstantsEqAlongAffineSpaceSquare.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.QuasiRefl
open HeckeCharacterZeroLocus.SiegelWeilU
section Form
variable {A : Type} [CommRing A] {n : Type} [Fintype n] {σ : A →+* A} {J : Matrix n n A}
theorem hform_eq_dot (x y : n → A) : hform σ J x y = (σ ∘ x) ⬝ᵥ J *ᵥ y := by
  simp [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
theorem comp_mulVec' (P : Matrix n n A) (x : n → A) : σ ∘ (P *ᵥ x) = P.map σ *ᵥ (σ ∘ x) := by
  funext i
  simp [mulVec, dotProduct]
theorem hform_mulVec' (P Q : Matrix n n A) (x y : n → A) :
    hform σ J (P *ᵥ x) (Q *ᵥ y) = hform σ (cT σ P * J * Q) x y := by
  rw [hform_eq_dot, hform_eq_dot, comp_mulVec', cT, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec _ (_ᵀ), vecMul_transpose]
theorem hform_sub_left (x d y : n → A) (c : A) :
    hform σ J (x - c • d) y = hform σ J x y - σ c * hform σ J d y := by
  simp [hform, Finset.mul_sum, sub_mul, mul_assoc]
theorem hform_sub_right (x d y : n → A) (c : A) :
    hform σ J x (y - c • d) = hform σ J x y - c * hform σ J x d := by
  simp [hform, Finset.mul_sum, mul_sub, mul_left_comm]
theorem hform_conj_symm (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x y : n → A) :
    σ (hform σ J x y) = hform σ J y x := by
  simp only [hform, map_sum, map_mul, hσ, hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end Form
section Refl
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {σ : A →+* A}
  {J : Matrix n n A}
def qrMat (σ : A →+* A) (J : Matrix n n A) (d : n → A) (c : A) : Matrix n n A :=
  1 - c • vecMulVec d ((σ ∘ d) ᵥ* J)
theorem qrMat_mulVec (d : n → A) (c : A) (z : n → A) :
    qrMat σ J d c *ᵥ z = z - (c * hform σ J d z) • d := by
  rw [qrMat, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hform_eq_dot, dotProduct_mulVec]
  funext i
  simp [mul_comm, mul_left_comm]
theorem ext_mulVec' {P Q : Matrix n n A} (h : ∀ z, P *ᵥ z = Q *ᵥ z) : P = Q := by
  ext i j
  simpa using congrFun (h (Pi.single j 1)) i
theorem qrMat_mul (d : n → A) {c c' : A} (hc : c + c' = c * c' * hform σ J d d) :
    qrMat σ J d c * qrMat σ J d c' = 1 := ext_mulVec' fun z => by
  rw [← mulVec_mulVec, qrMat_mulVec, qrMat_mulVec, hform_sub_right, one_mulVec]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-hform σ J d z * d i) * hc
theorem hform_single' (i j : n) :
    hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have : σ ∘ (Pi.single i 1 : n → A) = Pi.single i 1 := by
    funext k
    by_cases h : k = i <;> simp [h]
  rw [hform_eq_dot, this]
  simp
theorem qrMat_isometry (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (d : n → A) (c : A)
    (hc : c + σ c = c * σ c * hform σ J d d) :
    cT σ (qrMat σ J d c) * J * qrMat σ J d c = J := by
  ext i j
  rw [← hform_single' (σ := σ) (J := _ * J * _) i j, ← hform_mulVec', qrMat_mulVec, qrMat_mulVec,
    hform_sub_left, hform_sub_right, hform_sub_right, map_mul, hform_conj_symm hσ hJ,
    hform_single']
  linear_combination
    (-hform σ J (Pi.single i 1) d * hform σ J d (Pi.single j 1)) * hc
def qr (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (d : n → A) (c : A)
    (hc : c + σ c = c * σ c * hform σ J d d) : UJ σ J :=
  ⟨⟨qrMat σ J d c, qrMat σ J d (σ c), qrMat_mul d hc,
    qrMat_mul d (by linear_combination hc)⟩, qrMat_isometry hσ hJ d c hc⟩
end Refl
end GlobalTheory.CompanionTheory.SW.QuasiRefl


