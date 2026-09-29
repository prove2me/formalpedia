-- Prove2me | solution 1 for AdicCompletion.isRegularLocalRing_localization_atPrime_of_not_isMaximal_of_tame
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/08ac0f88-2897-53ad-9138-aece2df40bd5

import Mathlib
import Definitions.Def_AdicCompletionGaloisAction
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_Algebra_isUnramifiedAt_adicCompletion_of_forall_not_isMaximal_of_not_mem
import Theorems.Thm_IsIntegrallyClosed_isRegularLocalRing_localization_of_ne_maximalIdeal_of_ringKrullDim_le_two
import Theorems.Thm_IsRegularLocalRing_isDomain_and_isIntegrallyClosed_adicCompletion_of_ringKrullDim_eq_two
import Theorems.Thm_AdicCompletion_mem_nonZeroDivisors_algebraMap_of_mem_nonZeroDivisors_of_liesOver
import Theorems.Thm_Algebra_IsInvariant_isInvariant_adicCompletion_stabilizer_and_injective_and_finite
import Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing
import Theorems.Thm_AdicCompletion_isRegularLocalRing_localization_atPrime_of_mem_of_not_isMaximal_of_tame
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdicCompletion_isRegularLocalRing_localization_atPrime_of_not_isMaximal_of_tame
p2m_attr_erase "simp" "AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul"

set_option autoImplicit false

open IsLocalRing
open scoped Pointwise
open scoped AdicCompletion.GaloisAction

theorem solution {O : Type} [CommRing O] [IsRegularLocalRing O]
    (ϖ s : O) (hmaxO : maximalIdeal O = Ideal.span {ϖ, s}) (hdimO : ringKrullDim O = 2)
    (e : ℕ) (he : 0 < e) (heO : IsUnit (e : O))
    {C : Type} [CommRing C] [IsDomain C] [IsIntegrallyClosed C] [Algebra O C] [Module.Finite O C] [FaithfulSMul O C]
    {G : Type} [Group G] [Finite G] [MulSemiringAction G C] [SMulCommClass G O C] [FaithfulSMul G C]
    [Algebra.IsInvariant O C G]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)]
    (hI : Nat.card ↥((𝔫.inertia G).subgroupOf (MulAction.stabilizer G 𝔫)) = e) (hIcyc : IsCyclic ↥(𝔫.inertia G))
    (S : Type) [CommRing S] [IsLocalRing S] [Algebra C S] [IsLocalization.AtPrime S 𝔫] [Algebra O S] [IsScalarTower O C S]
    (hunr : ∀ (𝔮 : Ideal S) [𝔮.IsPrime], ¬ 𝔮.IsMaximal → s ∉ 𝔮.comap (algebraMap O S) → Algebra.IsUnramifiedAt O 𝔮) :
    ∀ (𝔭 : Ideal (AdicCompletion 𝔫 C)) [𝔭.IsPrime], ¬ 𝔭.IsMaximal → IsRegularLocalRing (Localization.AtPrime 𝔭) := by
  intro 𝔭 _ hnm
  classical
  by_cases hs𝔭 : algebraMap O (AdicCompletion 𝔫 C) s ∈ 𝔭
  · exact AdicCompletion.isRegularLocalRing_localization_atPrime_of_mem_of_not_isMaximal_of_tame
      ϖ s hmaxO hdimO e he heO 𝔫 hI 𝔭 hnm hs𝔭

  have hunr' : ∀ (𝔮 : Ideal S) [𝔮.IsPrime], ¬ 𝔮.IsMaximal → algebraMap O S s ∉ 𝔮 → Algebra.IsUnramifiedAt O 𝔮 :=
    fun 𝔮 _ h1 h2 => hunr 𝔮 h1 (by rwa [Ideal.mem_comap])
  have hunr : Algebra.IsUnramifiedAt (AdicCompletion (maximalIdeal O) O) 𝔭 :=
    Algebra.isUnramifiedAt_adicCompletion_of_forall_not_isMaximal_of_not_mem 𝔫 S s hunr' 𝔭 hnm hs𝔭
  haveI : IsNoetherianRing C := IsNoetherianRing.of_finite O C
  haveI : IsNoetherianRing (AdicCompletion 𝔫 C) := AdicCompletion.isNoetherianRing_of_isNoetherianRing 𝔫
  obtain ⟨hÔdom, hÔic, hÔnoeth, hÔdim⟩ :=
    IsRegularLocalRing.isDomain_and_isIntegrallyClosed_adicCompletion_of_ringKrullDim_eq_two O hdimO
  haveI := hÔdom
  haveI := hÔic
  haveI := hÔnoeth
  obtain ⟨-, -, hfin, -⟩ :=
    Algebra.IsInvariant.isInvariant_adicCompletion_stabilizer_and_injective_and_finite (O := O) (C := C) (G := G) 𝔫
  haveI := hfin
  haveI : Algebra.IsIntegral (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) :=
    Algebra.IsIntegral.of_finite _ _

  set 𝔯 : Ideal (AdicCompletion (maximalIdeal O) O) := 𝔭.under (AdicCompletion (maximalIdeal O) O) with h𝔯def
  haveI h𝔯p : 𝔯.IsPrime := Ideal.IsPrime.under (AdicCompletion (maximalIdeal O) O) 𝔭
  haveI : 𝔭.LiesOver 𝔯 := ⟨rfl⟩
  have h𝔯m : 𝔯 ≠ maximalIdeal (AdicCompletion (maximalIdeal O) O) := by
    intro h
    apply hnm
    have hmx : (𝔭.comap (algebraMap (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C))).IsMaximal := by
      show 𝔯.IsMaximal
      rw [h]
      exact IsLocalRing.maximalIdeal.isMaximal (AdicCompletion (maximalIdeal O) O)
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap 𝔭 hmx

  have hAreg : IsRegularLocalRing (Localization.AtPrime 𝔯) :=
      IsIntegrallyClosed.isRegularLocalRing_localization_of_ne_maximalIdeal_of_ringKrullDim_le_two hÔdim.le 𝔯 h𝔯m
  have hsA : (Submodule.spanFinrank (maximalIdeal (Localization.AtPrime 𝔯)) : WithBot ℕ∞) = 𝔯.height := by
    rw [hAreg.spanFinrank_maximalIdeal, IsLocalization.AtPrime.ringKrullDim_eq_height 𝔯 (Localization.AtPrime 𝔯)]
  have hsA' : (Submodule.spanFinrank (maximalIdeal (Localization.AtPrime 𝔯)) : ℕ∞) = 𝔯.height := by
    exact_mod_cast hsA
  have hht : 𝔯.height ≤ 1 := by
    have hlt : 𝔯 < maximalIdeal (AdicCompletion (maximalIdeal O) O) := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal h𝔯p.ne_top) h𝔯m
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have h2 : ((maximalIdeal (AdicCompletion (maximalIdeal O) O)).height : WithBot ℕ∞) ≤ 2 := Ideal.height_le_ringKrullDim_of_isPrime.trans hÔdim.le
    have h2' : (maximalIdeal (AdicCompletion (maximalIdeal O) O)).height ≤ 2 := WithBot.coe_le_coe.1 (by rw [WithBot.coe_ofNat]; exact h2)
    have h3 : 𝔯.height + 1 ≤ 2 := h1.trans h2'
    cases hq : 𝔯.height using ENat.recTopCoe with
    | top => rw [hq] at h3; simp at h3
    | coe n => rw [hq] at h3; norm_cast at h3 ⊢; omega

  letI : Algebra (Localization.AtPrime 𝔯) (Localization.AtPrime 𝔭) := Localization.AtPrime.algebraOfLiesOver 𝔯 𝔭
  have hmapeq : 𝔯.map (algebraMap (AdicCompletion (maximalIdeal O) O) (Localization.AtPrime 𝔭)) = maximalIdeal (Localization.AtPrime 𝔭) :=
    ((Algebra.isUnramifiedAt_iff_map_eq (AdicCompletion (maximalIdeal O) O) 𝔯 𝔭).1 hunr).2
  have hmapA : (maximalIdeal (Localization.AtPrime 𝔯)).map
      (algebraMap (Localization.AtPrime 𝔯) (Localization.AtPrime 𝔭)) = maximalIdeal (Localization.AtPrime 𝔭) := by
    rw [← hmapeq, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hs : Submodule.spanFinrank (maximalIdeal (Localization.AtPrime 𝔭)) ≤
      Submodule.spanFinrank (maximalIdeal (Localization.AtPrime 𝔯)) := by
    rw [← hmapA]
    exact Ideal.spanFinrank_map_le_of_fg _ (IsNoetherian.noetherian _)

  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (Localization.AtPrime 𝔭) ?_
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭 (Localization.AtPrime 𝔭)]

  by_cases h0 : 𝔯 = ⊥
  ·
    have hq0 : 𝔯.height = 0 := by rw [h0]; exact Ideal.height_bot
    have hA0 : Submodule.spanFinrank (maximalIdeal (Localization.AtPrime 𝔯)) = 0 := by
      have h := hsA'
      rw [hq0] at h
      exact_mod_cast h
    have hB0 : Submodule.spanFinrank (maximalIdeal (Localization.AtPrime 𝔭)) = 0 := Nat.le_zero.1 (hA0 ▸ hs)
    rw [hB0, Nat.cast_zero]
    exact_mod_cast (zero_le : (0 : ℕ∞) ≤ 𝔭.height)
  ·
    obtain ⟨π, hπ𝔯, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    have hπ𝔭 : algebraMap (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) π ∈ 𝔭 := hπ𝔯
    have hπnzd : algebraMap (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) π ∈ nonZeroDivisors (AdicCompletion 𝔫 C) :=
      AdicCompletion.mem_nonZeroDivisors_algebraMap_of_mem_nonZeroDivisors_of_liesOver (O := O) (C := C) 𝔫 π
        (mem_nonZeroDivisors_of_ne_zero hπ0)
    have hnotmin : 𝔭 ∉ minimalPrimes (AdicCompletion 𝔫 C) := fun hmin =>
      Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hmin) hπ𝔭 hπnzd
    have h𝔭1 : 1 ≤ 𝔭.height := ENat.one_le_iff_ne_zero.2 fun h => hnotmin (Ideal.height_eq_zero_iff.1 h)
    have hs1 : (Submodule.spanFinrank (maximalIdeal (Localization.AtPrime 𝔭)) : ℕ∞) ≤ 1 := by
      have h := (Nat.cast_le (α := ℕ∞)).2 hs
      exact h.trans (hsA'.trans_le hht)
    exact_mod_cast hs1.trans h𝔭1

end S_AdicCompletion_isRegularLocalRing_localization_atPrime_of_not_isMaximal_of_tame
end P2MW
export P2MW.S_AdicCompletion_isRegularLocalRing_localization_atPrime_of_not_isMaximal_of_tame (solution)
