-- Prove2me | solution 1 for Algebra.IsStandardSmoothOfRelativeDimension.isDedekindDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/ddb2f965-4097-5321-9fb6-9b7fee39554d

import Mathlib
import Theorems.Thm_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_IsStandardSmoothOfRelativeDimension_isDedekindDomain

universe u v

theorem S17L1cP.dvr_atPrime {k : Type u} {S : Type v} [Field k] [CommRing S] [IsDomain S] [Algebra k S]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k S] (m : Ideal S) [m.IsMaximal] :
    IsDiscreteValuationRing (Localization.AtPrime m) := by
  obtain ⟨_, h⟩ := Algebra.IsStandardSmoothOfRelativeDimension.isDiscreteValuationRing_localization_atPrime
    (k := k) m
  exact h

namespace S17L1cP

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [IsDomain S] [Algebra k S]
  [Algebra.IsStandardSmoothOfRelativeDimension 1 k S]

include k in
theorem isNoetherianRing' : IsNoetherianRing S := by
  haveI : Algebra.IsStandardSmooth k S := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  haveI : Algebra.FiniteType k S := inferInstance
  exact Algebra.FiniteType.isNoetherianRing k S

include k in

theorem isMaximal_of_isPrime' (P : Ideal S) (hP : P ≠ ⊥) [hp : P.IsPrime] : P.IsMaximal := by
  obtain ⟨m, hm, hPm⟩ := Ideal.exists_le_maximal P hp.ne_top
  haveI := S17L1cP.dvr_atPrime (k := k) m
  have hdisj : Disjoint (m.primeCompl : Set S) (P : Set S) := by
    rw [Set.disjoint_left]; intro x hx hxP; exact hx (hPm hxP)
  haveI hPm_prime : (P.map (algebraMap S (Localization.AtPrime m))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl _ P hp hdisj
  have hcomap : (P.map (algebraMap S (Localization.AtPrime m))).comap (algebraMap S _) = P :=
    IsLocalization.comap_map_of_isPrime_disjoint m.primeCompl _ hp hdisj
  have hPm_ne : P.map (algebraMap S (Localization.AtPrime m)) ≠ ⊥ := by
    intro h0
    apply hP
    rw [← hcomap, h0, Ideal.comap_bot_of_injective _ (IsLocalization.injective (Localization.AtPrime m) m.primeCompl_le_nonZeroDivisors)]

  have hmax : (P.map (algebraMap S (Localization.AtPrime m))).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hPm_ne hPm_prime
  have heq : P.map (algebraMap S (Localization.AtPrime m)) = IsLocalRing.maximalIdeal _ :=
    IsLocalRing.eq_maximalIdeal hmax
  have : P = m := by
    rw [← hcomap, heq]
    exact Localization.AtPrime.comap_maximalIdeal
  rw [this]; exact hm

include k in
theorem dimensionLEOne : Ring.DimensionLEOne S :=
  ⟨fun {P} hP hp => isMaximal_of_isPrime' (k := k) P hP⟩

include k in
theorem isDedekindDomainDvr : IsDedekindDomainDvr S := by
  haveI := isNoetherianRing' (k := k) (S := S)
  refine { (inferInstance : IsNoetherian S S) with is_dvr_at_nonzero_prime := ?_ }
  intro P hP hp
  haveI := isMaximal_of_isPrime' (k := k) P hP
  exact S17L1cP.dvr_atPrime (k := k) P

end S17L1cP

theorem solution {k : Type u} {S : Type v} [Field k] [CommRing S] [IsDomain S] [Algebra k S]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k S] : IsDedekindDomain S := by
  haveI := S17L1cP.isDedekindDomainDvr (k := k) (S := S)
  infer_instance

end S_Algebra_IsStandardSmoothOfRelativeDimension_isDedekindDomain
end P2MW
export P2MW.S_Algebra_IsStandardSmoothOfRelativeDimension_isDedekindDomain (solution)
