-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:01:47.87637+00:00
-- url     : https://prove2.me/theorems/face0d20-fabf-4c57-ae29-a0f62430f33b
-- title:
--   Capelli Coordinates
-- statement:
--   Definitions and structural lemmas for Capelli Coordinates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliCoordinates.lean

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_map_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_map_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace CapelliCoordinates
section Parts
variable {n : ℕ}
theorem hpart1_add (H Z W : Matrix (Fin n) (Fin n) ℂ) : hpart1 H (Z + W) = hpart1 H Z + hpart1 H W := by
  simp only [hpart1, conjTranspose_add, Matrix.mul_add, Matrix.add_mul, smul_sub, smul_add]
  abel
theorem hpart2_add (H Z W : Matrix (Fin n) (Fin n) ℂ) : hpart2 H (Z + W) = hpart2 H Z + hpart2 H W := by
  simp only [hpart2, conjTranspose_add, Matrix.mul_add, Matrix.add_mul, smul_add]
  abel
theorem inv2I : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
  have h : (2 * Complex.I) * (-Complex.I / 2) = 1 := by
    linear_combination (-1 : ℂ) * Complex.I_sq
  exact (eq_one_div_of_mul_eq_one_right h).symm
theorem hpart1_smul (H Z : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    hpart1 H (c • Z) = c.re • hpart1 H Z - c.im • hpart2 H Z := by
  have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
  have hs : star c = (c.re : ℂ) - (c.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  simp only [hpart1, hpart2, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, ← Complex.coe_smul, inv2I]
  rw [hs]
  match_scalars <;> first
    | ring1
    | linear_combination (1 / 2 : ℂ) * hc
    | linear_combination (-1 / 2 : ℂ) * hc
    | linear_combination (-Complex.I / 2) * hc + (-(c.im : ℂ) / 2) * Complex.I_sq
    | linear_combination ((c.im : ℂ) / 2) * Complex.I_sq
    | linear_combination (Complex.I / 2) * hc + ((c.im : ℂ) / 2) * Complex.I_sq
    | linear_combination (-(c.im : ℂ) / 2) * Complex.I_sq
theorem hpart2_smul (H Z : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    hpart2 H (c • Z) = c.re • hpart2 H Z + c.im • hpart1 H Z := by
  have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
  have hs : star c = (c.re : ℂ) - (c.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  simp only [hpart1, hpart2, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, ← Complex.coe_smul, inv2I]
  rw [hs]
  match_scalars <;> first
    | ring1
    | linear_combination (1 / 2 : ℂ) * hc
    | linear_combination (-1 / 2 : ℂ) * hc
    | linear_combination (-Complex.I / 2) * hc + (-(c.im : ℂ) / 2) * Complex.I_sq
    | linear_combination ((c.im : ℂ) / 2) * Complex.I_sq
    | linear_combination (Complex.I / 2) * hc + ((c.im : ℂ) / 2) * Complex.I_sq
    | linear_combination (-(c.im : ℂ) / 2) * Complex.I_sq
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def cx (H : Matrix (Fin n) (Fin n) ℂ) (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] E) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] E where
  toFun := fun Z => L (hpart1 H Z) + Complex.I • L (hpart2 H Z)
  map_add' := fun Z W => by
    rw [hpart1_add, hpart2_add, map_add, map_add, smul_add]
    abel
  map_smul' := fun c Z => by
    rw [hpart1_smul, hpart2_smul, map_sub, map_add, map_smul, map_smul, map_smul, map_smul, RingHom.id_apply]
    have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
    conv_rhs => rw [hc]
    simp only [← Complex.coe_smul, smul_add, add_smul, smul_smul]
    have h : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have e : ((c.re : ℂ) + (c.im : ℂ) * Complex.I) * Complex.I = (c.re : ℂ) * Complex.I - (c.im : ℂ) := by
      linear_combination (c.im : ℂ) * h
    rw [e, sub_smul, mul_comm Complex.I (c.re : ℂ), mul_comm Complex.I (c.im : ℂ)]
    abel
end Parts
section Sup
variable {k r : ℕ} {i : Fin (r + 1)}
def Sup (k r : ℕ) (i : Fin (r + 1)) (Z : Mx k r) : Prop :=
  ∀ p, ¬ Qx2.inV k r i p → Z *ᵥ bvec p = 0 ∧ (Hpk k r * Zᴴ * Hpk k r) *ᵥ bvec p = 0
end Sup
section Lin
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
end Lin
end CapelliCoordinates
namespace CapelliCoordinates
section Cap
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
end Cap
end CapelliCoordinates
namespace CapelliCoordinates
section Frame
variable {k r : ℕ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)}
end Frame
end CapelliCoordinates
end Formalism.FourierDecayAlt.P


