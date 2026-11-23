-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:05.84282+00:00
-- url     : https://prove2.me/theorems/89296382-8cb6-4060-8631-a3a0637013ee
-- title:
--   Exists Oscillator Action Unitary Group Hermitian
-- statement:
--   Definitions and structural lemmas for Exists Oscillator Action Unitary Group Hermitian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionUnitaryGroupHermitian.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairingsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CartanInvolutionConjOfPosDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThreeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianCongrInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProjEqSelfOfAnnihilated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
namespace GlobalTheory.RealWeil.UnitaryOsc
section Transport
variable {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
end Transport
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def mvL (g : Matrix ι ι ℂ) : (ι → ℂ) →L[ℝ] (ι → ℂ) :=
  LinearMap.toContinuousLinearMap ((Matrix.mulVecLin g).restrictScalars ℝ)
omit [DecidableEq ι] in
@[simp] theorem mvL_apply (g : Matrix ι ι ℂ) (v : ι → ℂ) : mvL g v = g *ᵥ v := rfl
omit [DecidableEq ι] in
theorem form_mulVec (H a : Matrix ι ι ℂ) (x y : ι → ℂ) :
    star (a *ᵥ y) ⬝ᵥ H *ᵥ a *ᵥ x = star y ⬝ᵥ (aᴴ * H * a) *ᵥ x := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
def crd (ι : Type) [Fintype ι] : EuclideanSpace ℂ ι ≃L[ℝ] (ι → ℂ) := PiLp.continuousLinearEquiv 2 ℝ fun _ : ι => ℂ
omit [DecidableEq ι] in
theorem inner_crd (x y : EuclideanSpace ℂ ι) : ⟪x, y⟫ = (star (crd ι x) ⬝ᵥ crd ι y).re := by
  rw [PiLp.inner_apply, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [crd, mul_comm]
def kL (g : Matrix ι ι ℂ) : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι :=
  ((crd ι).symm : (ι → ℂ) →L[ℝ] EuclideanSpace ℂ ι) ∘L mvL g ∘L (crd ι : EuclideanSpace ℂ ι →L[ℝ] (ι → ℂ))
omit [DecidableEq ι] in
theorem crd_kL (g : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) : crd ι (kL g v) = g *ᵥ crd ι v := by
  simp [kL]
theorem kL_one : kL (1 : Matrix ι ι ℂ) = 1 :=
  ContinuousLinearMap.ext fun v => (crd ι).injective (by rw [crd_kL, one_mulVec]; rfl)
omit [DecidableEq ι] in
theorem kL_mul (g g' : Matrix ι ι ℂ) : kL (g * g') = kL g * kL g' :=
  ContinuousLinearMap.ext fun v => (crd ι).injective (by
    rw [ContinuousLinearMap.mul_apply, crd_kL, crd_kL, crd_kL, mulVec_mulVec])
theorem norm_kL {g : Matrix ι ι ℂ} (hg : gᴴ * g = 1) (v : EuclideanSpace ℂ ι) : ‖kL g v‖ = ‖v‖ := by
  have := form_mulVec 1 g (crd ι v) (crd ι v)
  rw [mul_one, hg, one_mulVec, one_mulVec] at this
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_crd, inner_crd, crd_kL, this]
def cplx (s : Matrix ι ι ℂ) (h1 : sᴴ = s) (h2 : s * s = 1) : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := (kL (I • s) : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
      norm_map' := norm_kL (by
        rw [conjTranspose_smul, h1, smul_mul_smul_comm, h2]
        simp) } rfl
def uGrp (H : Matrix ι ι ℂ) : Subgroup (Matrix ι ι ℂ)ˣ where
  carrier := {g | (g : Matrix ι ι ℂ)ᴴ * H * g = H}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, conjTranspose_mul] at ha hb ⊢
    calc _ = (b : Matrix ι ι ℂ)ᴴ * ((a : Matrix ι ι ℂ)ᴴ * H * a) * b := by simp only [mul_assoc]
      _ = H := by rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc _ = ((a⁻¹ : (Matrix ι ι ℂ)ˣ) : Matrix ι ι ℂ)ᴴ * ((a : Matrix ι ι ℂ)ᴴ * H * a) * (a⁻¹ : (Matrix ι ι ℂ)ˣ) := by
          rw [ha]
      _ = ((a : Matrix ι ι ℂ) * (a⁻¹ : (Matrix ι ι ℂ)ˣ).1)ᴴ * H * ((a : Matrix ι ι ℂ) * (a⁻¹ : (Matrix ι ι ℂ)ˣ).1) := by
          simp only [mul_assoc, conjTranspose_mul]
      _ = H := by simp
def kU (H : Matrix ι ι ℂ) : uGrp H →* (EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) where
  toFun g := kL (g.1 : Matrix ι ι ℂ)
  map_one' := kL_one
  map_mul' _ _ := kL_mul _ _
end GlobalTheory.RealWeil.UnitaryOsc
end


