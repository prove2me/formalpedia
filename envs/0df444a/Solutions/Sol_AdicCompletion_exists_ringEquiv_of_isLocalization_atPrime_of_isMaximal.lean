-- Prove2me | solution 1 for AdicCompletion.exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/10db3a88-90db-52b3-b27c-290ab535e84e

import Mathlib
import Definitions.Def_PolynomialCompletion
import Definitions.Def_AdicCompletionRingFunctoriality
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdicCompletion_exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal
set_option autoImplicit false

namespace AdicCompletion p2m_export "AdicCompletion" "map of congr localizationEquiv localizationEquiv_of mapₐ_of mapAlgEquiv mapAlgEquiv_apply" namespace LocComplAux end AdicCompletion.LocComplAux
p2m_open_scoped "AdicCompletion" in
open IsLocalRing in

theorem AdicCompletion.LocComplAux.map_maximalIdeal_le_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) : (maximalIdeal R).map (e : R →+* S) ≤ maximalIdeal S := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  rw [mem_maximalIdeal, mem_nonunits_iff] at hx
  intro hu
  exact hx (by simpa using hu.map e.symm)

theorem solution
    {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    (𝔓 : Ideal B) [𝔓.IsMaximal] [IsLocalRing S] [IsLocalization.AtPrime S 𝔓] :
    ∃ T : AdicCompletion 𝔓 B ≃+* AdicCompletion (IsLocalRing.maximalIdeal S) S,
      ∀ b : B, T (algebraMap B (AdicCompletion 𝔓 B) b)
        = algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (algebraMap B S b) := by

  let L := Localization.AtPrime 𝔓
  let e : L ≃ₐ[B] S := IsLocalization.algEquiv 𝔓.primeCompl L S
  have he : (IsLocalRing.maximalIdeal L).map (e : L →ₐ[B] S) ≤ IsLocalRing.maximalIdeal S :=
    AdicCompletion.LocComplAux.map_maximalIdeal_le_of_ringEquiv e.toRingEquiv
  have he' : (IsLocalRing.maximalIdeal S).map (e.symm : S →ₐ[B] L) ≤ IsLocalRing.maximalIdeal L :=
    AdicCompletion.LocComplAux.map_maximalIdeal_le_of_ringEquiv e.symm.toRingEquiv
  let T₂ : AdicCompletion (IsLocalRing.maximalIdeal L) L ≃ₐ[B] AdicCompletion (IsLocalRing.maximalIdeal S) S :=
    AdicCompletion.mapAlgEquiv (IsLocalRing.maximalIdeal L) (IsLocalRing.maximalIdeal S) e he he'
  refine ⟨(AdicCompletion.localizationEquiv 𝔓).trans T₂.toRingEquiv, fun b => ?_⟩
  rw [RingEquiv.trans_apply]
  change T₂ (AdicCompletion.localizationEquiv 𝔓 (AdicCompletion.of 𝔓 B b)) =
    AdicCompletion.of (IsLocalRing.maximalIdeal S) S (algebraMap B S b)
  rw [AdicCompletion.localizationEquiv_of]
  change AdicCompletion.mapAlgEquiv (IsLocalRing.maximalIdeal L) (IsLocalRing.maximalIdeal S) e he he'
    (AdicCompletion.of _ _ (algebraMap B L b)) = _
  rw [AdicCompletion.mapAlgEquiv_apply, AdicCompletion.mapₐ_of]
  congr 1
  exact e.commutes b

end S_AdicCompletion_exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal
end P2MW
export P2MW.S_AdicCompletion_exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal (solution)
