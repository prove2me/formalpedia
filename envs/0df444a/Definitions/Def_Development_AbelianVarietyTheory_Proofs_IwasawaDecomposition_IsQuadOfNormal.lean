-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfNormal
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfNormal
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:14:45.878949+00:00
-- url     : https://prove2.me/theorems/c2452371-e72f-4972-913b-b3c2f8811a7e
-- title:
--   Is Quad Of Normal
-- statement:
--   Definitions and structural lemmas for Is Quad Of Normal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsQuadOfNormal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
noncomputable section
namespace GlobalTheory.Mem.Lift.Normal
variable {ι : Type}
theorem real_lin_smul (l : (ι → ℂ) →ₗ[ℝ] ℂ) (c : ℂ) (z : ι → ℂ) :
    l (c • z) = c.re * l z + c.im * l (I • z) := by
  have hc : c • z = c.re • z + c.im • (I • z) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  rw [hc, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
theorem real_lin_I_I (l : (ι → ℂ) →ₗ[ℝ] ℂ) (z : ι → ℂ) : l (I • I • z) = - l z := by
  rw [smul_smul, I_mul_I, neg_one_smul, map_neg]
def linPart (l : (ι → ℂ) →ₗ[ℝ] ℂ) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun z := l z - I * l (I • z)
  map_add' x y := by simp only [smul_add, map_add]; ring
  map_smul' c z := by
    rw [smul_comm I c z, real_lin_smul l c z, real_lin_smul l c (I • z), real_lin_I_I, RingHom.id_apply, smul_eq_mul]
    conv_rhs => rw [← Complex.re_add_im c]
    linear_combination (c.im * l (I • z)) * I_mul_I
def antiPart (l : (ι → ℂ) →ₗ[ℝ] ℂ) : (ι → ℂ) →ₗ⋆[ℂ] ℂ where
  toFun z := l z + I * l (I • z)
  map_add' x y := by simp only [smul_add, map_add]; ring
  map_smul' c z := by
    rw [smul_comm I c z, real_lin_smul l c z, real_lin_smul l c (I • z), real_lin_I_I, smul_eq_mul]
    have : (starRingEnd ℂ) c = c.re - c.im * I := by
      apply Complex.ext <;> simp
    rw [this]
    linear_combination (c.im * l (I • z)) * I_mul_I
variable [Fintype ι] [DecidableEq ι]
def nC (X : Matrix ι ι ℂ) (i : ι × ι × Bool × Bool) : ℂ :=
  X i.1 i.2.1 * (-(1 / (4 * π))) * (if i.2.2.1 then -I else 1) * (if i.2.2.2 then I else 1)
def nP (i : ι × ι × Bool × Bool) : ι → ℂ :=
  if i.2.2.1 then I • Pi.single i.1 1 else Pi.single i.1 1
def nQ (H : Matrix ι ι ℂ) (i : ι × ι × Bool × Bool) : ι → ℂ :=
  if i.2.2.2 then I • H⁻¹ *ᵥ Pi.single i.2.1 1 else H⁻¹ *ᵥ Pi.single i.2.1 1
def omH (H : Matrix ι ι ℂ) : (ι → ℂ) →L[ℝ] (ι → ℂ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((ι → ℂ) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun x y : ι → ℂ => (star y ⬝ᵥ H *ᵥ x).im)
        (fun x x' y => by simp [mulVec_add])
        (fun r x y => by simp [mulVec_smul])
        (fun x y y' => by simp)
        (fun r x y => by simp))
end GlobalTheory.Mem.Lift.Normal
end


