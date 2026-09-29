-- Prove2me | solution 1 for Algebra.map_span_le_radical_mul_map_comap_one_div_traceDual_of_isUnramifiedAt_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/ec198f5b-c9ef-5088-8130-448f45302d13

import Mathlib
import Theorems.Thm_Algebra_exists_mem_comap_one_div_traceDual_mul_eq_mul_of_height_eq_one_of_charZero
import Theorems.Thm_Algebra_isPrincipal_map_comap_one_div_traceDual_of_uniqueFactorizationMonoid
import Theorems.Thm_Algebra_isUnramifiedAt_iff_not_le_comap_one_div_traceDual_of_free_of_isIntegrallyClosed
import Theorems.Thm_Algebra_exists_le_height_eq_one_of_comap_one_div_traceDual_le_of_free_of_isIntegrallyClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_map_span_le_radical_mul_map_comap_one_div_traceDual_of_isUnramifiedAt_of_charZero

set_option autoImplicit false

universe u

namespace KAAux

open UniqueFactorizationMonoid

theorem radical_span_singleton_eq {T : Type*} [CommRing T] [IsDomain T] [UniqueFactorizationMonoid T] [NormalizationMonoid T]
    {a : T} (ha : a ≠ 0) : (Ideal.span ({a} : Set T)).radical = Ideal.span {radical a} := by
  classical
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_span_singleton]
    rcases eq_or_ne x 0 with rfl | hx0
    · exact dvd_zero _
    obtain ⟨k, hk⟩ := (Ideal.mem_radical_iff.mp hx)
    rw [Ideal.mem_span_singleton] at hk
    have h1 : radical a ∣ radical (x ^ k) := radical_dvd_radical hk (pow_ne_zero _ hx0)
    rcases eq_or_ne k 0 with rfl | hk0
    · rw [pow_zero] at hk
      have hu : IsUnit a := isUnit_of_dvd_one hk
      rw [radical_of_isUnit hu]; exact one_dvd _
    rw [radical_pow x hk0] at h1
    exact h1.trans radical_dvd_self
  · rw [Ideal.span_singleton_le_iff_mem, Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨haP, hP⟩
    rw [Ideal.span_singleton_le_iff_mem] at haP

    have hane : ¬ IsUnit a ∨ IsUnit a := em' _
    rcases hane with hna | hua
    ·
      have hassoc := prod_normalizedFactors ha
      obtain ⟨u, hu⟩ := hassoc
      have hmem : (normalizedFactors a).prod ∈ P := by
        have : (normalizedFactors a).prod * (u : T) ∈ P := by rw [hu]; exact haP
        exact (hP.mem_or_mem this).elim id (fun h => absurd (Ideal.eq_top_of_isUnit_mem _ h u.isUnit) hP.ne_top)
      obtain ⟨p, hpmem, hpP⟩ := (hP.multiset_prod_mem_iff_exists_mem _).mp hmem
      have hpf : p ∈ primeFactors a := (mem_primeFactors).mpr hpmem
      have hpdvd : p ∣ radical a := by
        unfold radical
        exact Finset.dvd_prod_of_mem id hpf
      obtain ⟨c, hc⟩ := hpdvd
      rw [hc]; exact Ideal.mul_mem_right _ _ hpP
    · exact absurd (Ideal.eq_top_of_isUnit_mem _ haP hua) hP.ne_top

end KAAux

namespace KAMain

open IsLocalRing UniqueFactorizationMonoid

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem main
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S] [Module.Free R S]
    (F : Type u) [Field F] [Algebra S F] [IsFractionRing S F] [Algebra K F] [Algebra R F]
    [IsScalarTower R K F] [IsScalarTower R S F] [Algebra.IsSeparable K F]
    (t : R) (ht : (Ideal.span ({t} : Set R)).IsPrime) [CharZero (R ⧸ Ideal.span ({t} : Set R))]
    (x : Ideal S) [x.IsPrime] [UniqueFactorizationMonoid (Localization.AtPrime x)]
    (hunr : ∀ (𝔔 : Ideal S) [𝔔.IsPrime], 𝔔 ≤ x → 𝔔.height = 1 → algebraMap R S t ∉ 𝔔 → Algebra.IsUnramifiedAt R 𝔔) :
    Ideal.map (algebraMap S (Localization.AtPrime x)) (Ideal.span {algebraMap R S t}) ≤
      (Ideal.map (algebraMap S (Localization.AtPrime x)) (Ideal.span {algebraMap R S t})).radical *
        Ideal.map (algebraMap S (Localization.AtPrime x)) ((1 / Submodule.traceDual R K (1 : Submodule S F) : Submodule S F).comap (Algebra.linearMap S F)) := by
  classical
  letI : StrongNormalizationMonoid (Localization.AtPrime x) :=
    UniqueFactorizationMonoid.normalizationMonoid
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  set D : Ideal S := ((1 / Submodule.traceDual R K (1 : Submodule S F) : Submodule S F).comap (Algebra.linearMap S F)) with hD
  set tS : S := algebraMap R S t with htS
  set tT : (Localization.AtPrime x) := algebraMap S (Localization.AtPrime x) tS with htT
  have hMle : x.primeCompl ≤ nonZeroDivisors S := Ideal.primeCompl_le_nonZeroDivisors x
  have hinjST : Function.Injective (algebraMap S (Localization.AtPrime x)) := IsLocalization.injective (Localization.AtPrime x) hMle
  rw [Ideal.map_span, Set.image_singleton, ← htT]

  have hQ : ∀ p : (Localization.AtPrime x), Prime p →
      ((Ideal.span ({p} : Set (Localization.AtPrime x))).comap (algebraMap S (Localization.AtPrime x))).IsPrime ∧
      (Ideal.span ({p} : Set (Localization.AtPrime x))).comap (algebraMap S (Localization.AtPrime x)) ≤ x ∧
      ((Ideal.span ({p} : Set (Localization.AtPrime x))).comap (algebraMap S (Localization.AtPrime x))).height = 1 := by
    intro p hp
    haveI hpI : (Ideal.span ({p} : Set (Localization.AtPrime x))).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
    refine ⟨Ideal.comap_isPrime _ _, ?_, ?_⟩
    · have h1 : Ideal.span ({p} : Set (Localization.AtPrime x)) ≤ maximalIdeal (Localization.AtPrime x) := IsLocalRing.le_maximalIdeal hpI.ne_top
      exact (Ideal.comap_mono h1).trans (IsLocalization.AtPrime.comap_maximalIdeal (Localization.AtPrime x) x).le
    · rw [show (Ideal.span ({p} : Set (Localization.AtPrime x))).comap (algebraMap S (Localization.AtPrime x)) = (Ideal.span ({p} : Set (Localization.AtPrime x))).under S from rfl,
        IsLocalization.height_under x.primeCompl (Ideal.span ({p} : Set (Localization.AtPrime x)))]
      apply le_antisymm (Ideal.height_span_singleton_le_one hp.not_unit)
      exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hp.ne_zero)

  by_cases htu : IsUnit tT
  · have htop : Ideal.span ({tT} : Set (Localization.AtPrime x)) = ⊤ := Ideal.span_singleton_eq_top.mpr htu
    rw [htop, Ideal.radical_top, Ideal.top_mul]

    have hDx : ¬ D ≤ x := by
      intro hle
      obtain ⟨Q, hQp, hQx, hQ1, hDQ⟩ :=
        Algebra.exists_le_height_eq_one_of_comap_one_div_traceDual_le_of_free_of_isIntegrallyClosed R K S F x hle
      haveI := hQp
      have htQ : tS ∉ Q := by
        intro h
        have : tT ∈ Q.map (algebraMap S (Localization.AtPrime x)) := Ideal.mem_map_of_mem _ h
        have hle' : Q.map (algebraMap S (Localization.AtPrime x)) ≤ maximalIdeal (Localization.AtPrime x) := by
          rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.map_mono hQx
        exact (IsLocalRing.mem_maximalIdeal _).mp (hle' this) htu
      exact (Algebra.isUnramifiedAt_iff_not_le_comap_one_div_traceDual_of_free_of_isIntegrallyClosed R K S F Q).mp
        (hunr Q hQx hQ1 htQ) hDQ
    obtain ⟨s, hsD, hsx⟩ := Set.not_subset.mp hDx
    have hsu : IsUnit (algebraMap S (Localization.AtPrime x) s) := IsLocalization.map_units (Localization.AtPrime x) (⟨s, hsx⟩ : x.primeCompl)
    exact (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hsD) hsu).symm.le

  rcases eq_or_ne tT 0 with h00 | ht0
  · rw [h00, Ideal.span_singleton_eq_bot.mpr rfl]; exact bot_le

  obtain ⟨δ, hδ⟩ := (Algebra.isPrincipal_map_comap_one_div_traceDual_of_uniqueFactorizationMonoid R K S F x).principal
  have hδ' : Ideal.map (algebraMap S (Localization.AtPrime x)) D = Ideal.span {δ} := by rw [hδ, Ideal.submodule_span_eq]
  have hδdvd : ∀ s ∈ D, δ ∣ algebraMap S (Localization.AtPrime x) s := fun s hs => by
    rw [← Ideal.mem_span_singleton, ← hδ']; exact Ideal.mem_map_of_mem _ hs
  rw [KAAux.radical_span_singleton_eq ht0]
  change Ideal.span {tT} ≤ Ideal.span {radical tT} * Ideal.map (algebraMap S (Localization.AtPrime x)) D
  rw [hδ', Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_le_span_singleton]

  obtain ⟨g, hg⟩ := (radical_dvd_self : radical tT ∣ tT)
  have hrad0 : radical tT ≠ 0 := radical_ne_zero
  have hg0 : g ≠ 0 := by intro h; apply ht0; rw [hg, h, mul_zero]

  have hfact : ∀ p : (Localization.AtPrime x), Prime p → normalize p = p → p ∣ δ → p ∣ tT ∧
      Multiset.count p (normalizedFactors δ) + 1 ≤ Multiset.count p (normalizedFactors tT) := by
    intro p hp hpn hpδ
    obtain ⟨hQp, hQx, hQ1⟩ := hQ p hp
    haveI := hQp

    have hpt : p ∣ tT := by
      by_contra hpt
      have htQ : tS ∉ (Ideal.span ({p} : Set (Localization.AtPrime x))).comap (algebraMap S (Localization.AtPrime x)) := by
        rw [Ideal.mem_comap, Ideal.mem_span_singleton]; exact hpt
      have hun := hunr _ hQx hQ1 htQ
      have hnD := (Algebra.isUnramifiedAt_iff_not_le_comap_one_div_traceDual_of_free_of_isIntegrallyClosed
        R K S F ((Ideal.span ({p} : Set (Localization.AtPrime x))).comap (algebraMap S (Localization.AtPrime x)))).mp hun
      obtain ⟨s, hsD, hsQ⟩ := Set.not_subset.mp hnD
      apply hsQ
      show s ∈ (Ideal.span ({p} : Set (Localization.AtPrime x))).comap (algebraMap S (Localization.AtPrime x))
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      exact hpδ.trans (hδdvd s hsD)
    refine ⟨hpt, ?_⟩
    have htQ : tS ∈ (Ideal.span ({p} : Set (Localization.AtPrime x))).comap (algebraMap S (Localization.AtPrime x)) := by
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]; exact hpt
    obtain ⟨s, hsD, u, huQ, z, hzQ, heq⟩ :=
      Algebra.exists_mem_comap_one_div_traceDual_mul_eq_mul_of_height_eq_one_of_charZero R K S F t ht
        ((Ideal.span ({p} : Set (Localization.AtPrime x))).comap (algebraMap S (Localization.AtPrime x))) hQ1 htQ
    have heqT : algebraMap S (Localization.AtPrime x) u * tT = algebraMap S (Localization.AtPrime x) s * algebraMap S (Localization.AtPrime x) z := by
      rw [htT, htS, ← map_mul, heq, map_mul]
    have hpu : ¬ p ∣ algebraMap S (Localization.AtPrime x) u := by
      intro h; apply huQ; rw [Ideal.mem_comap, Ideal.mem_span_singleton]; exact h
    have hpz : p ∣ algebraMap S (Localization.AtPrime x) z := by
      have := hzQ; rw [Ideal.mem_comap, Ideal.mem_span_singleton] at this; exact this
    have hu0 : algebraMap S (Localization.AtPrime x) u ≠ 0 := fun h => hpu (h ▸ dvd_zero p)
    have hz0 : algebraMap S (Localization.AtPrime x) z ≠ 0 := by
      intro h; rw [h, mul_zero] at heqT
      rcases mul_eq_zero.mp heqT with h1 | h1
      · exact hu0 h1
      · exact ht0 h1
    have hs0 : algebraMap S (Localization.AtPrime x) s ≠ 0 := by
      intro h; rw [h, zero_mul] at heqT
      rcases mul_eq_zero.mp heqT with h1 | h1
      · exact hu0 h1
      · exact ht0 h1
    have hδ0 : δ ≠ 0 := fun h => hs0 (eq_zero_of_zero_dvd (h ▸ hδdvd s hsD))
    have key : Multiset.count p (normalizedFactors (algebraMap S (Localization.AtPrime x) u)) + Multiset.count p (normalizedFactors tT) =
        Multiset.count p (normalizedFactors (algebraMap S (Localization.AtPrime x) s)) + Multiset.count p (normalizedFactors (algebraMap S (Localization.AtPrime x) z)) := by
      rw [← Multiset.count_add, ← normalizedFactors_mul hu0 ht0, heqT, normalizedFactors_mul hs0 hz0, Multiset.count_add]
    have hcu : Multiset.count p (normalizedFactors (algebraMap S (Localization.AtPrime x) u)) = 0 :=
      Multiset.count_eq_zero.mpr (fun h => hpu (dvd_of_mem_normalizedFactors h))
    have hcz : 1 ≤ Multiset.count p (normalizedFactors (algebraMap S (Localization.AtPrime x) z)) :=
      Multiset.one_le_count_iff_mem.mpr ((mem_normalizedFactors_iff' hz0).mpr ⟨hp.irreducible, hpn, hpz⟩)
    have hcs : Multiset.count p (normalizedFactors δ) ≤ Multiset.count p (normalizedFactors (algebraMap S (Localization.AtPrime x) s)) :=
      Multiset.le_iff_count.mp ((dvd_iff_normalizedFactors_le_normalizedFactors hδ0 hs0).mp (hδdvd s hsD)) p
    omega

  have hδ0 : δ ≠ 0 := by
    obtain ⟨p, hp, hpt⟩ := WfDvdMonoid.exists_irreducible_factor htu ht0
    obtain ⟨hQp, hQx, hQ1⟩ := hQ p hp.prime
    haveI := hQp
    have htQ : tS ∈ (Ideal.span ({p} : Set (Localization.AtPrime x))).comap (algebraMap S (Localization.AtPrime x)) := by
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]; exact hpt
    obtain ⟨s, hsD, u, huQ, z, hzQ, heq⟩ :=
      Algebra.exists_mem_comap_one_div_traceDual_mul_eq_mul_of_height_eq_one_of_charZero R K S F t ht
        ((Ideal.span ({p} : Set (Localization.AtPrime x))).comap (algebraMap S (Localization.AtPrime x))) hQ1 htQ
    intro hδz
    have hs0 : algebraMap S (Localization.AtPrime x) s = 0 := eq_zero_of_zero_dvd (hδz ▸ hδdvd s hsD)
    have heqT : algebraMap S (Localization.AtPrime x) u * tT = algebraMap S (Localization.AtPrime x) s * algebraMap S (Localization.AtPrime x) z := by
      rw [htT, htS, ← map_mul, heq, map_mul]
    rw [hs0, zero_mul] at heqT
    rcases mul_eq_zero.mp heqT with h1 | h1
    · apply huQ; rw [Ideal.mem_comap, Ideal.mem_span_singleton, h1]; exact dvd_zero p
    · exact ht0 h1

  suffices H : δ ∣ g by
    have : radical tT * δ ∣ radical tT * g := mul_dvd_mul_left _ H
    rwa [← hg] at this
  rw [dvd_iff_normalizedFactors_le_normalizedFactors hδ0 hg0, Multiset.le_iff_count]
  intro p
  by_cases hpδ : p ∈ normalizedFactors δ
  · have hp : Prime p := prime_of_normalized_factor p hpδ
    have hpn : normalize p = p := normalize_normalized_factor p hpδ
    obtain ⟨hpt, hcount⟩ := hfact p hp hpn (dvd_of_mem_normalizedFactors hpδ)
    have hct : Multiset.count p (normalizedFactors tT) =
        Multiset.count p (normalizedFactors (radical tT)) + Multiset.count p (normalizedFactors g) := by
      conv_lhs => rw [hg]
      rw [normalizedFactors_mul hrad0 hg0, Multiset.count_add]
    have hcr : Multiset.count p (normalizedFactors (radical tT)) ≤ 1 :=
      Multiset.nodup_iff_count_le_one.mp
        ((squarefree_iff_nodup_normalizedFactors hrad0).mp squarefree_radical) p
    omega
  · rw [Multiset.count_eq_zero.mpr hpδ]; exact Nat.zero_le _

end KAMain

open IsLocalRing

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S] [Module.Free R S]
    (F : Type u) [Field F] [Algebra S F] [IsFractionRing S F] [Algebra K F] [Algebra R F]
    [IsScalarTower R K F] [IsScalarTower R S F] [Algebra.IsSeparable K F]
    (t : R) (ht : (Ideal.span ({t} : Set R)).IsPrime) [CharZero (R ⧸ Ideal.span ({t} : Set R))]
    (x : Ideal S) [x.IsPrime] [UniqueFactorizationMonoid (Localization.AtPrime x)]
    (hunr : ∀ (𝔔 : Ideal S) [𝔔.IsPrime], 𝔔 ≤ x → 𝔔.height = 1 → algebraMap R S t ∉ 𝔔 → Algebra.IsUnramifiedAt R 𝔔) :
    Ideal.map (algebraMap S (Localization.AtPrime x)) (Ideal.span {algebraMap R S t}) ≤
      (Ideal.map (algebraMap S (Localization.AtPrime x)) (Ideal.span {algebraMap R S t})).radical *
        Ideal.map (algebraMap S (Localization.AtPrime x))
          (((1 / Submodule.traceDual R K (1 : Submodule S F) : Submodule S F).comap (Algebra.linearMap S F))) := by
  exact KAMain.main R K S F t ht x hunr

end S_Algebra_map_span_le_radical_mul_map_comap_one_div_traceDual_of_isUnramifiedAt_of_charZero
end P2MW
export P2MW.S_Algebra_map_span_le_radical_mul_map_comap_one_div_traceDual_of_isUnramifiedAt_of_charZero (solution)
