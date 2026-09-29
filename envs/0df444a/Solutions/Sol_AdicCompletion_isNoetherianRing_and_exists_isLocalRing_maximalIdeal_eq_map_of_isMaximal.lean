-- Prove2me | solution 1 for AdicCompletion.isNoetherianRing_and_exists_isLocalRing_maximalIdeal_eq_map_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/50960047-4e87-5474-84c5-54bd77ad75b1

import Mathlib
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdicCompletion_isNoetherianRing_and_exists_isLocalRing_maximalIdeal_eq_map_of_isMaximal

set_option autoImplicit false

theorem solution
    {C : Type*} [CommRing C] [IsNoetherianRing C] (𝔫 : Ideal C) [𝔫.IsMaximal] :
    IsNoetherianRing (AdicCompletion 𝔫 C) ∧
    ∃ _ : IsLocalRing (AdicCompletion 𝔫 C),
      IsLocalRing.maximalIdeal (AdicCompletion 𝔫 C) = 𝔫.map (algebraMap C (AdicCompletion 𝔫 C)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (AdicCompletion 𝔫 C)) (AdicCompletion 𝔫 C) ∧
      (IsLocalRing.maximalIdeal (AdicCompletion 𝔫 C)).comap (algebraMap C (AdicCompletion 𝔫 C)) = 𝔫 ∧
      Function.Surjective ((IsLocalRing.residue (AdicCompletion 𝔫 C)).comp (algebraMap C (AdicCompletion 𝔫 C))) := by
  classical

  have hfg : 𝔫.FG := IsNoetherian.noetherian 𝔫
  haveI hN : IsNoetherianRing (AdicCompletion 𝔫 C) :=
    AdicCompletion.isNoetherianRing_of_isNoetherianRing 𝔫

  haveI hcM : IsAdicComplete (𝔫.map (algebraMap C (AdicCompletion 𝔫 C))) (AdicCompletion 𝔫 C) :=
    (IsAdicComplete.map_algebraMap_iff 𝔫 (AdicCompletion 𝔫 C)).mpr (AdicCompletion.isAdicComplete hfg)

  have hker : RingHom.ker ((Ideal.quotEquivOfEq (pow_one 𝔫)).toRingHom.comp
      (AdicCompletion.evalₐ 𝔫 1).toRingHom) = 𝔫.map (algebraMap C (AdicCompletion 𝔫 C)) := by
    rw [← RingHom.comap_ker, RingEquiv.toRingHom_eq_coe, RingHom.ker_coe_equiv, ← RingHom.ker,
      show RingHom.ker (AdicCompletion.evalₐ 𝔫 1).toRingHom = RingHom.ker (AdicCompletion.evalₐ 𝔫 1)
        from rfl,
      AdicCompletion.ker_evalₐ_eq_map_pow 𝔫 hfg 1, pow_one]
  have hsurj1 : Function.Surjective ((Ideal.quotEquivOfEq (pow_one 𝔫)).toRingHom.comp
      (AdicCompletion.evalₐ 𝔫 1).toRingHom) :=
    (Ideal.quotEquivOfEq (pow_one 𝔫)).surjective.comp (AdicCompletion.surjective_evalₐ 𝔫 1)
  haveI hmaxM : (𝔫.map (algebraMap C (AdicCompletion 𝔫 C))).IsMaximal := by
    letI := Ideal.Quotient.field 𝔫
    rw [← hker]
    exact RingHom.ker_isMaximal_of_surjective _ hsurj1

  haveI hloc : IsLocalRing (AdicCompletion 𝔫 C) :=
    isLocalRing_of_isAdicComplete_maximal (𝔫.map (algebraMap C (AdicCompletion 𝔫 C)))
  have hmax : IsLocalRing.maximalIdeal (AdicCompletion 𝔫 C)
      = 𝔫.map (algebraMap C (AdicCompletion 𝔫 C)) :=
    (IsLocalRing.eq_maximalIdeal hmaxM).symm
  refine ⟨hN, hloc, hmax, hmax ▸ hcM, ?_, ?_⟩
  ·
    rw [hmax]
    refine (Ideal.IsMaximal.eq_of_le inferInstance ?_ Ideal.le_comap_map).symm
    exact Ideal.comap_ne_top _ hmaxM.ne_top
  ·
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨c, y, hy, rfl⟩ := AdicCompletion.exists_eq_algebraMap_add 𝔫 hfg 1 x
    refine ⟨c, ?_⟩
    rw [RingHom.comp_apply, IsLocalRing.residue_def]
    refine Ideal.Quotient.eq.mpr ?_
    rw [sub_add_cancel_left, neg_mem_iff, hmax]
    simpa only [pow_one] using hy

#print axioms solution

end S_AdicCompletion_isNoetherianRing_and_exists_isLocalRing_maximalIdeal_eq_map_of_isMaximal
end P2MW
export P2MW.S_AdicCompletion_isNoetherianRing_and_exists_isLocalRing_maximalIdeal_eq_map_of_isMaximal (solution)
