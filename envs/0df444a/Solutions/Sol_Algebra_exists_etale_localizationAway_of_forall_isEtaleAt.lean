-- Prove2me | solution 1 for Algebra.exists_etale_localizationAway_of_forall_isEtaleAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/6d7fea32-67f8-5e30-8ddd-996eade12ca0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_etale_localizationAway_of_forall_isEtaleAt

set_option autoImplicit false

open Polynomial PrimeSpectrum

universe u

theorem solution
    {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (hgen : ∀ (q : Ideal S) [q.IsPrime], q.comap (algebraMap R S) = ⊥ → Algebra.IsEtaleAt R q)
    (T : Finset (Ideal R)) (hT : ∀ p ∈ T, p.IsPrime)
    (hTet : ∀ p ∈ T, ∀ (q : Ideal S) [q.IsPrime], q.comap (algebraMap R S) = p → Algebra.IsEtaleAt R q) :
    ∃ c : R, c ≠ 0 ∧ (∀ p ∈ T, c ∉ p) ∧
      letI := (Localization.awayMap (algebraMap R S) c).toAlgebra
      Algebra.Etale (Localization.Away c) (Localization.Away (algebraMap R S c)) := by
  classical

  set Z : Set (PrimeSpectrum S) := (Algebra.etaleLocus R S)ᶜ with hZ
  have hZc : IsClosed Z := Algebra.isOpen_etaleLocus.isClosed_compl
  set W : Set (PrimeSpectrum R) := comap (algebraMap R S) '' Z with hW
  have hWc : IsClosed W :=
    isClosedMap_comap_of_isIntegral (algebraMap R S) (fun x => Algebra.IsIntegral.isIntegral (R := R) x) Z hZc
  set I : Ideal R := vanishingIdeal W with hI
  have hWI : zeroLocus (I : Set R) = W := by
    rw [hI, zeroLocus_vanishingIdeal_eq_closure, hWc.closure_eq]

  have key : ∀ (p : Ideal R) [p.IsPrime],
      (∀ (q : Ideal S) [q.IsPrime], q.comap (algebraMap R S) = p → Algebra.IsEtaleAt R q) → ¬ I ≤ p := by
    intro p _ hp hIp
    have hmem : (⟨p, inferInstance⟩ : PrimeSpectrum R) ∈ zeroLocus (I : Set R) := hIp
    rw [hWI] at hmem
    obtain ⟨q, hqZ, hq⟩ := hmem
    apply hqZ
    have hq' : q.asIdeal.comap (algebraMap R S) = p := congrArg PrimeSpectrum.asIdeal hq
    exact hp q.asIdeal hq'

  have havoid : ¬ ((I : Set R) ⊆ ⋃ p ∈ (↑(insert (⊥ : Ideal R) T) : Set (Ideal R)), ((p : Ideal R) : Set R)) := by
    rw [Ideal.subset_union_prime (⊥ : Ideal R) (⊥ : Ideal R) (fun p hp _ _ => ?_)]
    · rintro ⟨p, hp, hIp⟩
      rcases Finset.mem_insert.1 hp with rfl | hpT
      · exact key ⊥ (fun q _ hq => hgen q hq) hIp
      · haveI := hT p hpT
        exact key p (fun q _ hq => hTet p hpT q hq) hIp
    · rcases Finset.mem_insert.1 hp with rfl | hpT
      · exact Ideal.isPrime_bot
      · exact hT p hpT
  rw [Set.not_subset] at havoid
  obtain ⟨c, hcI, hc⟩ := havoid
  simp only [Set.mem_iUnion, SetLike.mem_coe, not_exists, Finset.coe_insert, Set.mem_insert_iff] at hc
  have hc0 : c ≠ 0 := fun h0 => hc ⊥ (Or.inl rfl) (by rw [h0]; exact Ideal.zero_mem _)
  have hcT : ∀ p ∈ T, c ∉ p := fun p hp => hc p (Or.inr hp)
  refine ⟨c, hc0, hcT, ?_⟩

  have hsub : ↑(basicOpen (algebraMap R S c)) ⊆ Algebra.etaleLocus R S := by
    intro q hq
    by_contra hqZ
    have hW' : comap (algebraMap R S) q ∈ W := ⟨q, hqZ, rfl⟩
    rw [← hWI] at hW'
    exact hq (hW' hcI)
  haveI hEt : Algebra.Etale R (Localization.Away (algebraMap R S c)) :=
    Algebra.basicOpen_subset_etaleLocus_iff_etale.mp hsub

  letI := (Localization.awayMap (algebraMap R S) c).toAlgebra
  haveI : IsScalarTower R (Localization.Away c) (Localization.Away (algebraMap R S c)) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_comp,
        ← IsScalarTower.algebraMap_eq])
  haveI : IsLocalization ((Submonoid.powers c).map (algebraMap R S)) (Localization.Away (algebraMap R S c)) := by
    rw [Submonoid.map_powers]; exact Localization.isLocalization
  haveI : Algebra.FormallyEtale (Localization.Away c) (Localization.Away (algebraMap R S c)) :=
    Algebra.FormallyEtale.localization_base (Submonoid.powers c)
  haveI : Algebra.Etale R (Localization.Away c) := Algebra.Etale.of_isLocalizationAway c
  haveI : Algebra.FinitePresentation (Localization.Away c) (Localization.Away (algebraMap R S c)) :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ _
  exact ⟨inferInstance, inferInstance⟩

end S_Algebra_exists_etale_localizationAway_of_forall_isEtaleAt
end P2MW
export P2MW.S_Algebra_exists_etale_localizationAway_of_forall_isEtaleAt (solution)
