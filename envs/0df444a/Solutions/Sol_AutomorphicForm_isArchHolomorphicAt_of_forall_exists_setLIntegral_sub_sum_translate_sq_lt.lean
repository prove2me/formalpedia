-- Prove2me | solution 1 for AutomorphicForm.isArchHolomorphicAt_of_forall_exists_setLIntegral_sub_sum_translate_sq_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ffe20255-abc5-57eb-8f69-6e030723d2da

import Mathlib
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Theorems.Thm_AutomorphicForm_isArchHolomorphicAt_of_forall_exists_setLIntegral_sub_sum_holomorphic_translate_sq_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isArchHolomorphicAt_of_forall_exists_setLIntegral_sub_sum_translate_sq_lt
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal Manifold

namespace Ws1
namespace H389

variable (K : Type) [Field K] [NumberField K]

theorem isLsXiFunction_const_mul {Z : Subgroup (AdeleRing (𝓞 K) K)ˣ} {ξ : Z →* ℂˣ} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsLsXiFunction (𝓞 K) K Z ξ φ) (a : ℂ) : IsLsXiFunction (𝓞 K) K Z ξ (fun y => a * φ y) :=
  ⟨fun γ g => by rw [hφ.left_invariant], fun z g => by rw [hφ.central_transform]; ring⟩

theorem hasArchCharacterAt₀_const_mul {w : InfinitePlace K} {χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : HasArchCharacterAt₀ K w χ φ) (a : ℂ) :
    HasArchCharacterAt₀ K w χ (fun y => a * φ y) :=
  fun k g => by
    show a * φ _ = _ * (a * φ g)
    rw [hφ k g]
    ring

theorem isArchHolomorphicAt_const_mul {w : InfinitePlace K} (hw : w.IsReal) {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsArchHolomorphicAt w hw φ) (a : ℂ) : IsArchHolomorphicAt w hw (fun y => a * φ y) := by
  intro g
  have hfun : (fun z : UpperHalfPlane => ((z.im : ℝ) : ℂ)⁻¹ * (a * φ (g * adelicArchGLInclAt K w
      (Matrix.GeneralLinearGroup.map
        ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
        (iwasawaSectionGL z))))) = a • (fun z : UpperHalfPlane => ((z.im : ℝ) : ℂ)⁻¹ * φ (g * adelicArchGLInclAt K w
      (Matrix.GeneralLinearGroup.map
        ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
        (iwasawaSectionGL z)))) := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  show MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : UpperHalfPlane => ((z.im : ℝ) : ℂ)⁻¹ * (a * φ (g * adelicArchGLInclAt K w
      (Matrix.GeneralLinearGroup.map
        ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
        (iwasawaSectionGL z)))))
  rw [hfun]
  exact (hφ g).const_smul a

end Ws1.H389

open Ws1.H389 in
theorem solution
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (φ φ' : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ) (hφ' : Continuous φ')
    (hφc : IsSmoothCuspAutomorphicFnAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      ξ φ)
    (hφ'c : IsSmoothCuspAutomorphicFnAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      ξ φ')
    (w : InfinitePlace K) (hw : w.IsReal)
    (hφw : HasArchCharacterAt₀ K w (archWeightOneAt hw) φ)
    (hφhol : IsArchHolomorphicAt w hw φ)
    (hφ'w : HasArchCharacterAt₀ K w (archWeightOneAt hw) φ')
    (happrox : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
        ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
            (‖φ' y - ∑ h ∈ s, l h * φ (y * h)‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 K) K) < ε) :
    IsArchHolomorphicAt w hw φ' := by
  classical

  have hφL : IsLsXiFunction (𝓞 K) K ⊤ ξ φ :=
    ((@lsXiMemberAt_iff (𝓞 K) K _ _ _ _ _ (glBorel (Fin 2) (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K) ⊤ ξ
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) φ).mp hφc.1.1).1
  have hφ'L : IsLsXiFunction (𝓞 K) K ⊤ ξ φ' :=
    ((@lsXiMemberAt_iff (𝓞 K) K _ _ _ _ _ (glBorel (Fin 2) (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K) ⊤ ξ
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) φ').mp hφ'c.1.1).1
  refine AutomorphicForm.isArchHolomorphicAt_of_forall_exists_setLIntegral_sub_sum_holomorphic_translate_sq_lt
    K c u d₁ d₂ T hd hcov ξ φ' hφ' hφ'L w hw hφ'w ?_
  intro ε hε
  obtain ⟨s, l, hlt⟩ := happrox ε hε
  let e := s.equivFin
  refine ⟨s.card, fun i y => l (e.symm i : AdelicGL2 (𝓞 K) K) * φ y, fun i => (e.symm i : AdelicGL2 (𝓞 K) K),
    fun i => ⟨continuous_const.mul hφ, isLsXiFunction_const_mul K hφL _, hasArchCharacterAt₀_const_mul K hφw _,
      isArchHolomorphicAt_const_mul K hw hφhol _⟩, ?_⟩
  have hsum : ∀ y : AdelicGL2 (𝓞 K) K,
      (∑ i : Fin s.card, l (e.symm i : AdelicGL2 (𝓞 K) K) * φ (y * (e.symm i : AdelicGL2 (𝓞 K) K)))
        = ∑ h ∈ s, l h * φ (y * h) := by
    intro y
    rw [← Finset.sum_coe_sort s (fun h => l h * φ (y * h))]
    exact Equiv.sum_comp e.symm (fun a : ↥s => l (a : AdelicGL2 (𝓞 K) K) * φ (y * (a : AdelicGL2 (𝓞 K) K)))
  simp_rw [hsum]
  exact hlt

end S_AutomorphicForm_isArchHolomorphicAt_of_forall_exists_setLIntegral_sub_sum_translate_sq_lt
end P2MW
export P2MW.S_AutomorphicForm_isArchHolomorphicAt_of_forall_exists_setLIntegral_sub_sum_translate_sq_lt (solution)
