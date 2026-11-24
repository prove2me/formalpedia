-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
-- name    : GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:42.644808+00:00
-- url     : https://prove2.me/theorems/a5cb43fe-958e-4e97-8e9c-942218a8b0b8
-- title:
--   Discr Neg And Abs Norm Mul
-- statement:
--   Definitions and structural lemmas for Discr Neg And Abs Norm Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DiscrNegAndAbsNormMul.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_RealEisensteinNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaPeriodLatticeClassPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Theta
namespace projectiveLineClassData
open NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding UpperHalfPlane
open scoped nonZeroDivisors ComplexConjugate
variable {K : Type} [Field K] [NumberField K]
section Embeddings
omit [NumberField K] in

theorem conjugate_ne (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0) : conjugate σ ≠ σ := by
  obtain ⟨x, hx⟩ := hσ
  intro h
  apply hx
  have h1 := congrArg (fun φ : K →+* ℂ => φ x) h
  simp only [conjugate_coe_eq] at h1
  exact Complex.conj_eq_iff_im.mp h1
end Embeddings
section Covolume
open EtaPeriodLatticeClass
def embPair (σ : K →+* ℂ) : Fin 2 → (K →ₐ[ℚ] ℂ) :=
  ![σ.toRatAlgHom, (conjugate σ).toRatAlgHom]
theorem embPair_bijective (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ∃ x : K, (σ x).im ≠ 0) : Function.Bijective (embPair σ) := by
  rw [Fintype.bijective_iff_injective_and_card, AlgHom.card, hK, Fintype.card_fin]
  have hne : σ.toRatAlgHom ≠ (conjugate σ).toRatAlgHom := fun h =>
    conjugate_ne σ hσ (RingHom.ext fun x => by
      have := DFunLike.congr_fun h x
      simpa [RingHom.toRatAlgHom_apply] using this.symm)
  refine ⟨fun i j hij => ?_, rfl⟩
  match i, j with
  | 0, 0 => rfl
  | 0, 1 => exact absurd hij hne
  | 1, 0 => exact absurd hij.symm hne
  | 1, 1 => rfl
def embEquiv (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0) :
    Fin 2 ≃ (K →ₐ[ℚ] ℂ) :=
  Equiv.ofBijective _ (embPair_bijective hK σ hσ)
end Covolume
section Covolume2
open EtaPeriodLatticeClass
end Covolume2
end projectiveLineClassData
end GroundTheory.Heights₂.Theta


