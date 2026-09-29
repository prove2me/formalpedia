-- Prove2me | solution 1 for AdicCompletion.exists_ringEquiv_of_isLocalization_of_comap_eq_of_comap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/c6b73c53-e649-5899-a2a5-822ea365e30f

import Mathlib
import Theorems.Thm_AdicCompletion_exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdicCompletion_exists_ringEquiv_of_isLocalization_of_comap_eq_of_comap_eq
p2m_attr_erase "simp" "AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply"

set_option autoImplicit false

theorem solution
    {A B Q : Type*} [CommRing A] [CommRing B] [CommRing Q] [Algebra A Q] [Algebra B Q]
    (M : Submonoid A) [IsLocalization M Q] (N : Submonoid B) [IsLocalization N Q]
    (P : Ideal A) [P.IsMaximal] (PB : Ideal B) [PB.IsMaximal]
    (𝔔 : Ideal Q) [𝔔.IsPrime]
    (hP : 𝔔.comap (algebraMap A Q) = P) (hPB : 𝔔.comap (algebraMap B Q) = PB) :
    ∃ T : AdicCompletion P A ≃+* AdicCompletion PB B,
      ∀ (a : A) (b : B), algebraMap A Q a = algebraMap B Q b →
        T (algebraMap A (AdicCompletion P A) a) = algebraMap B (AdicCompletion PB B) b := by
  subst hP hPB
  let T := Localization.AtPrime 𝔔
  haveI : IsScalarTower A Q T := inferInstance
  haveI : IsScalarTower B Q T := inferInstance
  have hA : IsLocalization.AtPrime T (𝔔.comap (algebraMap A Q)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M T 𝔔
  have hB : IsLocalization.AtPrime T (𝔔.comap (algebraMap B Q)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization N T 𝔔
  haveI := hA
  haveI := hB
  obtain ⟨TA, hTA⟩ := AdicCompletion.exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal (S := T) (𝔔.comap (algebraMap A Q))
  obtain ⟨TB, hTB⟩ := AdicCompletion.exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal (S := T) (𝔔.comap (algebraMap B Q))
  refine ⟨TA.trans TB.symm, fun a b hab => ?_⟩
  rw [RingEquiv.trans_apply, hTA, RingEquiv.symm_apply_eq, hTB]
  congr 1
  rw [IsScalarTower.algebraMap_apply A Q T, IsScalarTower.algebraMap_apply B Q T, hab]

end S_AdicCompletion_exists_ringEquiv_of_isLocalization_of_comap_eq_of_comap_eq
end P2MW
export P2MW.S_AdicCompletion_exists_ringEquiv_of_isLocalization_of_comap_eq_of_comap_eq (solution)
