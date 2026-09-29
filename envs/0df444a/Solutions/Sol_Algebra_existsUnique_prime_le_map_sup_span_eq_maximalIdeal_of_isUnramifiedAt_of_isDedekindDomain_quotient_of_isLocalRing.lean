-- Prove2me | solution 1 for Algebra.existsUnique_prime_le_map_sup_span_eq_maximalIdeal_of_isUnramifiedAt_of_isDedekindDomain_quotient_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/34fd1aa2-7779-5dd7-88eb-8dc61601ea82

import Mathlib
import Theorems.Thm_Algebra_map_span_le_radical_mul_map_comap_one_div_traceDual_of_isUnramifiedAt_of_charZero
import Theorems.Thm_Algebra_mk_mem_pow_ramificationIdx_sub_one_of_mem_comap_one_div_traceDual
import Theorems.Thm_IsLocalRing_uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_existsUnique_prime_le_map_sup_span_eq_maximalIdeal_of_isUnramifiedAt_of_isDedekindDomain_quotient_of_isLocalRing

set_option autoImplicit false

universe u

namespace CoreAux

open IsLocalRing UniqueFactorizationMonoid

theorem isUnit_of_isUnit_mk {T : Type*} [CommRing T] [IsLocalRing T] {I : Ideal T} (hI : I ≤ maximalIdeal T)
    {m : T} (h : IsUnit (Ideal.Quotient.mk I m)) : IsUnit m := by
  obtain ⟨q, hq⟩ := h.exists_right_inv
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq] at hq
  by_contra hm
  have h1 : m * q ∈ maximalIdeal T := Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).mpr hm)
  have : (1 : T) ∈ maximalIdeal T := by
    have := Ideal.sub_mem _ h1 (hI hq)
    rwa [sub_sub_cancel] at this
  exact (maximalIdeal.isMaximal T).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)

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

theorem exists_prime_radical_eq_span_and_span_pair_eq_maximalIdeal
    {T : Type*} [CommRing T] [IsDomain T] [IsNoetherianRing T] [IsLocalRing T] [UniqueFactorizationMonoid T]
    (ϖ t : T) [hϖp : (Ideal.span ({ϖ} : Set T)).IsPrime]
    [IsDiscreteValuationRing (T ⧸ Ideal.span ({ϖ} : Set T))]
    (htm : t ∈ maximalIdeal T) (hϖt : ¬ ϖ ∣ t)
    (D : Ideal T)
    (hKA : Ideal.span ({t} : Set T) ≤ (Ideal.span ({t} : Set T)).radical * D)
    (n : ℕ) (hn : Ideal.Quotient.mk (Ideal.span ({ϖ} : Set T)) t ∉ maximalIdeal (T ⧸ Ideal.span ({ϖ} : Set T)) ^ (n + 1))
    (hKB : D.map (Ideal.Quotient.mk (Ideal.span ({ϖ} : Set T))) ≤ maximalIdeal (T ⧸ Ideal.span ({ϖ} : Set T)) ^ (n - 1)) :
    ∃ p : T, Prime p ∧ (Ideal.span ({t} : Set T)).radical = Ideal.span {p} ∧
      Ideal.span {p, ϖ} = maximalIdeal T ∧
      ∀ Q : Ideal T, Q.IsPrime → t ∈ Q → ϖ ∉ Q → Q ≠ maximalIdeal T → Q = Ideal.span {p} := by
  classical
  letI : StrongNormalizationMonoid T := UniqueFactorizationMonoid.normalizationMonoid
  set I : Ideal T := Ideal.span ({ϖ} : Set T) with hI
  set mk := Ideal.Quotient.mk I with hmk
  have hϖnu : ¬ IsUnit ϖ := fun h => hϖp.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_span_singleton_self ϖ) h)
  have hIle : I ≤ maximalIdeal T := by
    rw [hI, Ideal.span_singleton_le_iff_mem]; exact (mem_maximalIdeal _).mpr hϖnu
  have ht0 : t ≠ 0 := fun h => hϖt (h ▸ dvd_zero ϖ)
  have htbar0 : mk t ≠ 0 := by
    rw [hmk, Ne, Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]; exact hϖt

  set r := radical t with hr
  have hrad : (Ideal.span ({t} : Set T)).radical = Ideal.span {r} := radical_span_singleton_eq ht0
  have htmem : t ∈ Ideal.span {r} * D := by
    rw [← hrad]; exact hKA (Ideal.mem_span_singleton_self t)
  obtain ⟨d, hdD, hrd⟩ := Ideal.mem_span_singleton_mul.mp htmem

  set v := IsDiscreteValuationRing.addVal (T ⧸ I) with hv
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.exists_irreducible (T ⧸ I)
  have hmu : maximalIdeal (T ⧸ I) = Ideal.span {u} := hu.maximalIdeal_eq
  have hvt : v (mk t) ≤ n := by
    have h1 : ¬ u ^ (n + 1) ∣ mk t := by
      intro h; apply hn; rw [hmu, Ideal.span_singleton_pow, Ideal.mem_span_singleton]; exact h
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hu, not_le] at h1
    have h2 : v (mk t) < (n : ℕ∞) + 1 := by simpa [hv] using h1
    have htop : v (mk t) ≠ ⊤ := by rw [hv, Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact htbar0
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hk] at h2 ⊢
    norm_cast at h2 ⊢
    omega
  have hvd : ((n - 1 : ℕ) : ℕ∞) ≤ v (mk d) := by
    have hdmem : mk d ∈ maximalIdeal (T ⧸ I) ^ (n - 1) := hKB (Ideal.mem_map_of_mem _ hdD)
    rw [hmu, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hdmem
    have := (IsDiscreteValuationRing.addVal_le_iff_dvd).mpr hdmem
    rwa [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hu, nsmul_eq_mul, mul_one] at this
  have hsum : v (mk r) + v (mk d) ≤ n := by
    rw [← hrd, map_mul, hv, IsDiscreteValuationRing.addVal_mul, ← hv] at hvt; exact hvt

  have hvr : v (mk r) ≤ 1 := by
    have hdtop : v (mk d) ≠ ⊤ := by
      rw [hv, Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
      intro h0; apply htbar0; rw [← hrd, map_mul, h0, mul_zero]
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hdtop
    have hrtop : v (mk r) ≠ ⊤ := by
      rw [hv, Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
      intro h0; apply htbar0; rw [← hrd, map_mul, h0, zero_mul]
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hrtop
    rw [← hm] at hsum hvd
    rw [← hk] at hsum ⊢
    norm_cast at hsum hvd ⊢
    omega

  have hfac_nu : ∀ p ∈ primeFactors t, 1 ≤ v (mk p) := by
    intro p hp
    have hpprime : Prime p := prime_of_normalized_factor p (mem_primeFactors.mp hp)
    rw [ENat.one_le_iff_ne_zero, hv, Ne, IsDiscreteValuationRing.addVal_eq_zero_iff]
    intro hunit
    exact hpprime.not_unit (isUnit_of_isUnit_mk hIle hunit)
  have hrprod : r = (primeFactors t).prod id := by rw [hr]; unfold radical; rfl
  have hvsum : v (mk r) = (primeFactors t).sum (fun p => v (mk p)) := by
    have key : ∀ s : Finset T, v (mk (s.prod id)) = s.sum (fun p => v (mk p)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [hv]
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, map_mul, hv, IsDiscreteValuationRing.addVal_mul, ← hv, ih]
        rfl
    rw [hrprod]; exact key _
  have hne : (primeFactors t).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, primeFactors_eq_empty_iff ht0]
    exact (mem_maximalIdeal _).mp htm

  have hcard : (primeFactors t).card = 1 := by
    have hle : ((primeFactors t).card : ℕ∞) ≤ 1 := by
      calc ((primeFactors t).card : ℕ∞) = (primeFactors t).sum (fun _ => (1 : ℕ∞)) := by simp
        _ ≤ (primeFactors t).sum (fun p => v (mk p)) := Finset.sum_le_sum hfac_nu
        _ = v (mk r) := hvsum.symm
        _ ≤ 1 := hvr
    have h1 : (primeFactors t).card ≤ 1 := by exact_mod_cast hle
    have h2 : 0 < (primeFactors t).card := Finset.card_pos.mpr hne
    omega
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard
  have hpmem : p ∈ primeFactors t := by rw [hp]; exact Finset.mem_singleton_self p
  have hpprime : Prime p := prime_of_normalized_factor p (mem_primeFactors.mp hpmem)
  have hrp : r = p := by rw [hrprod, hp, Finset.prod_singleton]; rfl
  have hvp : v (mk p) = 1 := by
    apply le_antisymm
    · rw [← hrp]; exact hvr
    · exact hfac_nu p hpmem

  have hmp : maximalIdeal (T ⧸ I) = Ideal.span {mk p} := by
    have hassoc : Associated (mk p) u := by
      rw [← IsDiscreteValuationRing.addVal_eq_iff_associated, ← hv, hvp, hv, IsDiscreteValuationRing.addVal_uniformizer hu]
    rw [hmu]; exact (Ideal.span_singleton_eq_span_singleton.mpr hassoc).symm
  have hmax : Ideal.span {p, ϖ} = maximalIdeal T := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact (mem_maximalIdeal _).mpr hpprime.not_unit
      · exact (mem_maximalIdeal _).mpr hϖnu
    · intro m hm
      have hmbar : mk m ∈ maximalIdeal (T ⧸ I) := by
        rw [mem_maximalIdeal, mem_nonunits_iff]
        exact fun h => (mem_maximalIdeal _).mp hm (isUnit_of_isUnit_mk hIle h)
      rw [hmp, Ideal.mem_span_singleton] at hmbar
      obtain ⟨c, hc⟩ := hmbar
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      rw [← map_mul, hmk, Ideal.Quotient.eq, hI, Ideal.mem_span_singleton] at hc
      obtain ⟨e, he⟩ := hc
      have : m = p * c + ϖ * e := by rw [← he]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
  refine ⟨p, hpprime, by rw [hrad, hrp], hmax, ?_⟩

  intro Q hQ htQ hϖQ hQne
  have hpQ : p ∈ Q := by
    have : (Ideal.span ({t} : Set T)).radical ≤ Q :=
      (hQ.radical_le_iff).mpr ((Ideal.span_singleton_le_iff_mem _).mpr htQ)
    rw [hrad, hrp, Ideal.span_singleton_le_iff_mem] at this
    exact this
  apply le_antisymm _ ((Ideal.span_singleton_le_iff_mem _).mpr hpQ)
  have hQle : Q ≤ maximalIdeal T := IsLocalRing.le_maximalIdeal hQ.ne_top
  have key : Q ≤ Ideal.span {p} ⊔ I • Q := by
    intro q hq
    have hq' : q ∈ Ideal.span {p, ϖ} := by rw [hmax]; exact hQle hq
    rw [Ideal.mem_span_pair] at hq'
    obtain ⟨a, b, hab⟩ := hq'
    have hbϖ : b * ϖ ∈ Q := by
      have : b * ϖ = q - a * p := by rw [← hab]; ring
      rw [this]; exact Q.sub_mem hq (Ideal.mul_mem_left _ _ hpQ)
    have hb : b ∈ Q := ((hQ.mem_or_mem hbϖ).resolve_right hϖQ)
    rw [← hab]
    refine Submodule.add_mem_sup (Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩) ?_
    rw [mul_comm]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ϖ) hb
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian Q) ?_ key
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]; exact hIle

end CoreAux

namespace CoreLocalAux

open IsLocalRing

@[reducible] noncomputable def quotAlg {S : Type u} [CommRing S] (T : Type u) [CommRing T] [Algebra S T]
    (I : Ideal S) (J : Ideal T) (h : I ≤ J.comap (algebraMap S T)) : Algebra (S ⧸ I) (T ⧸ J) :=
  (Ideal.quotientMap J (algebraMap S T) h).toAlgebra

theorem isLocalization_quotient {S : Type u} [CommRing S] [IsDomain S] (M : Submonoid S) (hM : M ≤ nonZeroDivisors S)
    (T : Type u) [CommRing T] [Algebra S T] [IsLocalization M T] (I : Ideal S) (J : Ideal T)
    (hJ : J = I.map (algebraMap S T)) :
    letI := quotAlg T I J (by rw [hJ]; exact Ideal.le_comap_map)
    IsLocalization (M.map (Ideal.Quotient.mk I)) (T ⧸ J) := by
  letI := quotAlg T I J (by rw [hJ]; exact Ideal.le_comap_map)
  have halg : ∀ b : S, algebraMap (S ⧸ I) (T ⧸ J) (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ (algebraMap S T b) :=
    fun _ => rfl
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    obtain ⟨m, hm, rfl⟩ := Submonoid.mem_map.mp hs
    rw [halg]
    exact (IsLocalization.map_units T (⟨m, hm⟩ : M)).map _
  · intro z
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨b, t⟩, hbt⟩ := IsLocalization.surj M w
    refine ⟨⟨Ideal.Quotient.mk _ b, ⟨Ideal.Quotient.mk _ (t : S), Submonoid.mem_map.mpr ⟨t, t.2, rfl⟩⟩⟩, ?_⟩
    show Ideal.Quotient.mk _ w * algebraMap _ _ (Ideal.Quotient.mk _ (t : S)) = algebraMap _ _ (Ideal.Quotient.mk _ b)
    rw [halg, halg, ← map_mul, hbt]
  · intro a₁ a₂ h
    obtain ⟨b₁, rfl⟩ := Ideal.Quotient.mk_surjective a₁
    obtain ⟨b₂, rfl⟩ := Ideal.Quotient.mk_surjective a₂
    rw [halg, halg, Ideal.Quotient.eq, hJ, ← map_sub, IsLocalization.mem_map_algebraMap_iff M T] at h
    obtain ⟨⟨⟨i, hi⟩, m⟩, hm⟩ := h

    have hm' : algebraMap S T ((m : S) * (b₁ - b₂)) = algebraMap S T i := by
      rw [map_mul, mul_comm]; exact hm
    have h2 : (m : S) * (b₁ - b₂) = i := IsLocalization.injective T hM hm'
    refine ⟨⟨Ideal.Quotient.mk _ (m : S), Submonoid.mem_map.mpr ⟨m, m.2, rfl⟩⟩, ?_⟩
    show Ideal.Quotient.mk _ (m : S) * Ideal.Quotient.mk _ b₁ = Ideal.Quotient.mk _ (m : S) * Ideal.Quotient.mk _ b₂
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub, h2]
    exact hi

end CoreLocalAux

namespace CoreLocal

open IsLocalRing

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem main
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S] [Module.Free R S]
    (F : Type u) [Field F] [Algebra S F] [IsFractionRing S F] [Algebra K F] [Algebra R F]
    [IsScalarTower R K F] [IsScalarTower R S F] [Algebra.IsSeparable K F]
    (ϖ t : R) (hϖ0 : ϖ ≠ 0) (hmax : maximalIdeal R = Ideal.span {ϖ, t})
    [hϖp : (Ideal.span ({ϖ} : Set R)).IsPrime] (hϖ : IsDiscreteValuationRing (R ⧸ Ideal.span ({ϖ} : Set R)))
    (htp : (Ideal.span ({t} : Set R)).IsPrime) [CharZero (R ⧸ Ideal.span ({t} : Set R))]
    (hfib : IsDedekindDomain (S ⧸ Ideal.span ({algebraMap R S ϖ} : Set S)))
    (x : Ideal S) [x.IsMaximal]
    (hunr : ∀ (𝔔 : Ideal S) [𝔔.IsPrime], 𝔔 ≤ x → 𝔔.height = 1 → algebraMap R S t ∉ 𝔔 → Algebra.IsUnramifiedAt R 𝔔) :
    ∃ 𝔔 : Ideal S, 𝔔.IsPrime ∧ 𝔔 ≤ x ∧ algebraMap R S t ∈ 𝔔 ∧ algebraMap R S ϖ ∉ 𝔔 ∧
      (∀ (O : Type u) [CommRing O] [IsLocalRing O] [Algebra S O] [IsLocalization.AtPrime O x],
        Ideal.map (algebraMap S O) 𝔔 ⊔ Ideal.span {algebraMap S O (algebraMap R S ϖ)} = maximalIdeal O) ∧
      ∀ 𝔔' : Ideal S, 𝔔'.IsPrime → 𝔔' ≤ x → algebraMap R S t ∈ 𝔔' → algebraMap R S ϖ ∉ 𝔔' → 𝔔' = 𝔔 := by
  classical

  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite _ _
  have hmapI : (Ideal.span ({ϖ} : Set R)).map (algebraMap R S) = Ideal.span ({algebraMap R S ϖ} : Set S) := by
    rw [Ideal.map_span, Set.image_singleton]
  have hfib' : IsDedekindDomain (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S)) := by rw [hmapI]; exact hfib
  haveI hISp : ((Ideal.span ({ϖ} : Set R)).map (algebraMap R S)).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp hfib'.toIsDomain
  have hxR : x.comap (algebraMap R S) = maximalIdeal R := by
    haveI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) x
    exact IsLocalRing.eq_maximalIdeal inferInstance
  have hϖR : ϖ ∈ maximalIdeal R := by rw [hmax]; exact Ideal.subset_span (by simp)
  have htR : t ∈ maximalIdeal R := by rw [hmax]; exact Ideal.subset_span (by simp)
  have hϖx : algebraMap R S ϖ ∈ x := by rw [← Ideal.mem_comap, hxR]; exact hϖR
  have htx : algebraMap R S t ∈ x := by rw [← Ideal.mem_comap, hxR]; exact htR
  have hIx : (Ideal.span ({ϖ} : Set R)).map (algebraMap R S) ≤ x := by
    rw [hmapI, Ideal.span_singleton_le_iff_mem]; exact hϖx

  have htI : t ∉ Ideal.span ({ϖ} : Set R) := by
    intro ht
    have hmI : maximalIdeal R ≤ Ideal.span ({ϖ} : Set R) := by
      rw [hmax, Ideal.span_le]; rintro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact Ideal.mem_span_singleton_self _
      · exact ht
    have heq : Ideal.span ({ϖ} : Set R) = maximalIdeal R := le_antisymm (IsLocalRing.le_maximalIdeal hϖp.ne_top) hmI
    haveI : (Ideal.span ({ϖ} : Set R)).IsMaximal := heq ▸ maximalIdeal.isMaximal R
    exact IsDiscreteValuationRing.not_isField (R ⧸ Ideal.span ({ϖ} : Set R))
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance)

  haveI : Module.FaithfullyFlat R S := inferInstance
  have htnot : algebraMap R S t ∉ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S) := by
    intro h
    apply htI
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) (Ideal.span ({ϖ} : Set R)), Ideal.mem_comap]
    exact h

  have hMle : x.primeCompl ≤ nonZeroDivisors S := Ideal.primeCompl_le_nonZeroDivisors x
  have hJ : Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x)) =
      ((Ideal.span ({ϖ} : Set R)).map (algebraMap R S)).map (algebraMap S (Localization.AtPrime x)) := by
    rw [hmapI, Ideal.map_span, Set.image_singleton]
  letI algST : Algebra (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S)) ((Localization.AtPrime x) ⧸ Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x))) := CoreLocalAux.quotAlg (Localization.AtPrime x) _ _ (by rw [hJ]; exact Ideal.le_comap_map)
  haveI hlocT : IsLocalization (x.primeCompl.map (Ideal.Quotient.mk ((Ideal.span ({ϖ} : Set R)).map (algebraMap R S)))) ((Localization.AtPrime x) ⧸ Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x))) :=
    CoreLocalAux.isLocalization_quotient x.primeCompl hMle (Localization.AtPrime x) _ _ hJ

  set xb : Ideal (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S)) := x.map (Ideal.Quotient.mk _) with hxb
  haveI hxbmax : xb.IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk ((Ideal.span ({ϖ} : Set R)).map (algebraMap R S)))
      Ideal.Quotient.mk_surjective (inferInstance : x.IsMaximal) with h | h
    · exfalso
      have : x = ⊤ := by
        have h2 := congrArg (Ideal.comap (Ideal.Quotient.mk ((Ideal.span ({ϖ} : Set R)).map (algebraMap R S)))) h
        rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.comap_top, ← RingHom.ker_eq_comap_bot,
          Ideal.mk_ker, sup_eq_left.mpr hIx] at h2
      exact (inferInstance : x.IsMaximal).ne_top this
    · exact h
  have hxbcomap : xb.comap (Ideal.Quotient.mk _) = x := by
    rw [hxb, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr hIx]
  have hsub : xb.primeCompl = x.primeCompl.map (Ideal.Quotient.mk ((Ideal.span ({ϖ} : Set R)).map (algebraMap R S))) := by
    ext s
    constructor
    · intro hs
      obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective s
      refine Submonoid.mem_map.mpr ⟨s', ?_, rfl⟩
      intro hs'; exact hs (Ideal.mem_map_of_mem _ hs')
    · rintro hs hsx
      obtain ⟨s', hs', rfl⟩ := Submonoid.mem_map.mp hs
      apply hs'
      show s' ∈ x
      rw [← hxbcomap]; exact Ideal.mem_comap.mpr hsx
  haveI hlocT' : IsLocalization.AtPrime ((Localization.AtPrime x) ⧸ Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x))) xb := by
    show IsLocalization xb.primeCompl _
    rw [hsub]; exact hlocT
  have hM' : x.primeCompl.map (Ideal.Quotient.mk ((Ideal.span ({ϖ} : Set R)).map (algebraMap R S))) ≤ nonZeroDivisors (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S)) := by
    rw [← hsub]; exact Ideal.primeCompl_le_nonZeroDivisors xb
  haveI : IsDomain (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S)) := hfib'.toIsDomain
  haveI hTbdom : IsDomain ((Localization.AtPrime x) ⧸ Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x))) := IsLocalization.isDomain_of_le_nonZeroDivisors (S := ((Localization.AtPrime x) ⧸ Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x)))) hM'
  have hxb0 : xb ≠ ⊥ := by
    intro h0
    apply htnot
    have : Ideal.Quotient.mk ((Ideal.span ({ϖ} : Set R)).map (algebraMap R S)) (algebraMap R S t) ∈ xb :=
      Ideal.mem_map_of_mem _ htx
    rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  haveI := hfib'
  have hTbdvr : IsDiscreteValuationRing ((Localization.AtPrime x) ⧸ Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x))) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S)) hxb0 ((Localization.AtPrime x) ⧸ Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x)))
  haveI hϖTp : (Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x))).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp hTbdom
  haveI := hTbdvr
  haveI hufd : UniqueFactorizationMonoid (Localization.AtPrime x) :=
    IsLocalRing.uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient (algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ))

  have hKA := Algebra.map_span_le_radical_mul_map_comap_one_div_traceDual_of_isUnramifiedAt_of_charZero
    R K S F t htp x hunr
  rw [Ideal.map_span, Set.image_singleton] at hKA

  set pS : Ideal (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S)) := ((maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span ({ϖ} : Set R)))).map
      (algebraMap (R ⧸ Ideal.span ({ϖ} : Set R)) (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S))) with hpS
  have hpSeq : pS = Ideal.span {Ideal.Quotient.mk ((Ideal.span ({ϖ} : Set R)).map (algebraMap R S)) (algebraMap R S t)} := by
    rw [hpS, hmax, Ideal.map_span (Ideal.Quotient.mk (Ideal.span ({ϖ} : Set R))), Set.image_insert_eq, Set.image_singleton,
      Ideal.map_span (algebraMap (R ⧸ Ideal.span ({ϖ} : Set R)) (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S))), Set.image_insert_eq, Set.image_singleton,
      Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.Quotient.algebraMap_quotient_map_quotient]
    have h0 : (Ideal.Quotient.mk ((Ideal.span ({ϖ} : Set R)).map (algebraMap R S))) (algebraMap R S ϖ) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self ϖ))
    rw [h0, Ideal.span_insert, Ideal.span_singleton_eq_bot.mpr rfl, bot_sup_eq]
  have hpS0 : pS ≠ ⊥ := by
    rw [hpSeq, Ne, Ideal.span_singleton_eq_bot, Ideal.Quotient.eq_zero_iff_mem]; exact htnot
  have hfin : FiniteMultiplicity xb pS := FiniteMultiplicity.of_not_isUnit (Ideal.isUnit_iff.not.mpr hxbmax.ne_top) hpS0
  set n : ℕ := multiplicity xb pS with hn
  have hn1 : pS ≤ xb ^ n := Ideal.le_of_dvd (pow_multiplicity_dvd xb pS)
  have hn2 : ¬ pS ≤ xb ^ (n + 1) := fun h => hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self n) (Ideal.dvd_iff_le.mpr h)

  have hunrϖ : ∀ (𝔔 : Ideal S) [𝔔.IsPrime], algebraMap R S ϖ ∈ 𝔔 → 𝔔.height = 1 → Algebra.IsUnramifiedAt R 𝔔 := by
    intro 𝔔 _ hϖ𝔔 h1
    have hle : (Ideal.span ({ϖ} : Set R)).map (algebraMap R S) ≤ 𝔔 := by
      rw [hmapI, Ideal.span_singleton_le_iff_mem]; exact hϖ𝔔
    have hI0 : (Ideal.span ({ϖ} : Set R)).map (algebraMap R S) ≠ ⊥ := by
      rw [hmapI, Ne, Ideal.span_singleton_eq_bot]
      intro h0; exact hϖ0 (FaithfulSMul.algebraMap_injective R S (by rw [h0, map_zero]))
    have heq : 𝔔 = (Ideal.span ({ϖ} : Set R)).map (algebraMap R S) := by
      by_contra hne
      have hlt : (Ideal.span ({ϖ} : Set R)).map (algebraMap R S) < 𝔔 := lt_of_le_of_ne hle (Ne.symm hne)
      have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      rw [h1] at h2
      have h3 : ((Ideal.span ({ϖ} : Set R)).map (algebraMap R S)).height ≠ 0 := by
        rw [Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff]; exact hI0
      revert h2 h3
      generalize ((Ideal.span ({ϖ} : Set R)).map (algebraMap R S)).height = k
      intro h2 h3
      induction k using ENat.recTopCoe with
      | top => exact absurd h2 (by simp)
      | coe k => norm_cast at h2 h3; omega
    subst heq
    exact hunr _ hIx h1 htnot

  have hKB : (Ideal.map (algebraMap S (Localization.AtPrime x)) ((1 / Submodule.traceDual R K (1 : Submodule S F) : Submodule S F).comap (Algebra.linearMap S F))).map (Ideal.Quotient.mk (Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x)))) ≤
      maximalIdeal ((Localization.AtPrime x) ⧸ Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x))) ^ (n - 1) := by
    have e1 : (Ideal.map (algebraMap S (Localization.AtPrime x)) ((1 / Submodule.traceDual R K (1 : Submodule S F) : Submodule S F).comap (Algebra.linearMap S F))).map (Ideal.Quotient.mk (Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x)))) =
        (Ideal.map (Ideal.Quotient.mk ((Ideal.span ({ϖ} : Set R)).map (algebraMap R S))) ((1 / Submodule.traceDual R K (1 : Submodule S F) : Submodule S F).comap (Algebra.linearMap S F))).map (algebraMap (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S)) ((Localization.AtPrime x) ⧸ Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x)))) := by
      have hc : ((Ideal.Quotient.mk (Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x))))).comp (algebraMap S (Localization.AtPrime x)) = (algebraMap (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S)) ((Localization.AtPrime x) ⧸ Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x)))).comp (Ideal.Quotient.mk ((Ideal.span ({ϖ} : Set R)).map (algebraMap R S))) :=
        RingHom.ext fun _ => rfl
      rw [Ideal.map_map, Ideal.map_map, hc]
    rw [e1]
    have e2 : Ideal.map (Ideal.Quotient.mk ((Ideal.span ({ϖ} : Set R)).map (algebraMap R S))) ((1 / Submodule.traceDual R K (1 : Submodule S F) : Submodule S F).comap (Algebra.linearMap S F)) ≤ xb ^ (n - 1) := by
      rw [Ideal.map_le_iff_le_comap]
      intro s hs
      exact Algebra.mk_mem_pow_ramificationIdx_sub_one_of_mem_comap_one_div_traceDual R K S F ϖ hϖ0 hϖ hfib' hunrϖ s hs xb n hn1
    calc (Ideal.map (Ideal.Quotient.mk ((Ideal.span ({ϖ} : Set R)).map (algebraMap R S))) ((1 / Submodule.traceDual R K (1 : Submodule S F) : Submodule S F).comap (Algebra.linearMap S F))).map (algebraMap (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S)) ((Localization.AtPrime x) ⧸ Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x))))
        ≤ (xb ^ (n - 1)).map (algebraMap (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S)) ((Localization.AtPrime x) ⧸ Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x)))) := Ideal.map_mono e2
      _ = (xb.map (algebraMap (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S)) ((Localization.AtPrime x) ⧸ Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x))))) ^ (n - 1) := Ideal.map_pow _ _ _
      _ = maximalIdeal ((Localization.AtPrime x) ⧸ Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x))) ^ (n - 1) := by rw [IsLocalization.AtPrime.map_eq_maximalIdeal xb ((Localization.AtPrime x) ⧸ Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x)))]
  have hnT : Ideal.Quotient.mk (Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x))) (algebraMap S (Localization.AtPrime x) (algebraMap R S t)) ∉
      maximalIdeal ((Localization.AtPrime x) ⧸ Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x))) ^ (n + 1) := by
    intro h
    apply hn2
    rw [hpSeq, Ideal.span_singleton_le_iff_mem]
    have hprim : (xb ^ (n + 1)).IsPrimary := Ideal.isPrimary_of_isMaximal_radical (by
      rw [Ideal.radical_pow _ (Nat.succ_ne_zero n), hxbmax.isPrime.radical]; exact hxbmax)
    have hdis : Disjoint (xb.primeCompl : Set (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S))) (xb ^ (n + 1) : Ideal (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S))) := by
      rw [Set.disjoint_left]; intro s hs hs'; exact hs (Ideal.pow_le_self (Nat.succ_ne_zero n) hs')
    have key := IsLocalization.under_map_of_isPrimary_disjoint (M := xb.primeCompl) (S := ((Localization.AtPrime x) ⧸ Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x)))) hprim hdis
    rw [← key]
    show algebraMap (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S)) ((Localization.AtPrime x) ⧸ Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x))) ((Ideal.Quotient.mk ((Ideal.span ({ϖ} : Set R)).map (algebraMap R S))) (algebraMap R S t)) ∈ (xb ^ (n + 1)).map (algebraMap (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S)) ((Localization.AtPrime x) ⧸ Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x))))
    rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal xb ((Localization.AtPrime x) ⧸ Ideal.span ({algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)} : Set (Localization.AtPrime x)))]
    exact h

  have htm : algebraMap S (Localization.AtPrime x) (algebraMap R S t) ∈ maximalIdeal (Localization.AtPrime x) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ htx
  have hϖt : ¬ algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ) ∣ algebraMap S (Localization.AtPrime x) (algebraMap R S t) := by
    intro h
    apply htnot
    have h1 : algebraMap S (Localization.AtPrime x) (algebraMap R S t) ∈ ((Ideal.span ({ϖ} : Set R)).map (algebraMap R S)).map (algebraMap S (Localization.AtPrime x)) := by
      rw [← hJ, Ideal.mem_span_singleton]; exact h
    rw [← IsLocalization.under_map_of_isPrime_disjoint x.primeCompl (Localization.AtPrime x) hISp
      (Set.disjoint_left.mpr fun s hs hs' => hs (hIx hs'))]
    exact h1
  obtain ⟨p, hpprime, hrad, hspan, huniq⟩ :=
    CoreAux.exists_prime_radical_eq_span_and_span_pair_eq_maximalIdeal
      (algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)) (algebraMap S (Localization.AtPrime x) (algebraMap R S t)) htm hϖt
      (Ideal.map (algebraMap S (Localization.AtPrime x)) ((1 / Submodule.traceDual R K (1 : Submodule S F) : Submodule S F).comap (Algebra.linearMap S F))) hKA n hnT hKB

  have hdisj : Disjoint (x.primeCompl : Set S) (x : Set S) := Set.disjoint_left.mpr fun s hs hs' => hs hs'
  haveI hpT : (Ideal.span ({p} : Set (Localization.AtPrime x))).IsPrime := (Ideal.span_singleton_prime hpprime.ne_zero).mpr hpprime
  have hpm : Ideal.span ({p} : Set (Localization.AtPrime x)) ≤ maximalIdeal (Localization.AtPrime x) := by
    rw [← hspan]; exact Ideal.span_mono (by simp)
  have hcomapm : (maximalIdeal (Localization.AtPrime x)).comap (algebraMap S (Localization.AtPrime x)) = x := IsLocalization.AtPrime.comap_maximalIdeal (Localization.AtPrime x) x
  refine ⟨(Ideal.span ({p} : Set (Localization.AtPrime x))).comap (algebraMap S (Localization.AtPrime x)), Ideal.comap_isPrime _ _, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Ideal.comap_mono hpm).trans hcomapm.le
  · rw [Ideal.mem_comap, ← Ideal.span_singleton_le_iff_mem, ← hrad]; exact Ideal.le_radical
  · rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    intro h
    apply hϖt
    have hϖirr : Irreducible (algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)) := by
      have : Prime (algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)) := by
        rw [← Ideal.span_singleton_prime]; · exact hϖTp
        intro h0; apply hϖ0
        have h1 : algebraMap R S ϖ = 0 := IsLocalization.injective (Localization.AtPrime x) hMle (by rw [map_zero]; exact h0)
        exact FaithfulSMul.algebraMap_injective R S (by rw [h1, map_zero])
      exact this.irreducible
    exact (hpprime.irreducible.associated_of_dvd hϖirr h).symm.dvd.trans (Ideal.mem_span_singleton.mp (by
      rw [← Ideal.span_singleton_le_iff_mem, ← hrad]; exact Ideal.le_radical))
  · intro O _ _ _ _
    let e : (Localization.AtPrime x) ≃ₐ[S] O := IsLocalization.algEquiv x.primeCompl (Localization.AtPrime x) O
    have hmapQ : Ideal.map (algebraMap S (Localization.AtPrime x)) ((Ideal.span ({p} : Set (Localization.AtPrime x))).comap (algebraMap S (Localization.AtPrime x))) = Ideal.span {p} :=
      IsLocalization.map_comap x.primeCompl (Localization.AtPrime x) _
    have h1 : Ideal.map (e : (Localization.AtPrime x) →+* O) (Ideal.map (algebraMap S (Localization.AtPrime x)) ((Ideal.span ({p} : Set (Localization.AtPrime x))).comap (algebraMap S (Localization.AtPrime x))) ⊔
        Ideal.span {algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)}) = Ideal.map (e : (Localization.AtPrime x) →+* O) (maximalIdeal (Localization.AtPrime x)) := by
      rw [hmapQ, ← Ideal.span_insert, hspan]
    rw [Ideal.map_sup, Ideal.map_map, Ideal.map_span, Set.image_singleton] at h1
    have h2 : (e : (Localization.AtPrime x) →+* O).comp (algebraMap S (Localization.AtPrime x)) = algebraMap S O := e.toAlgHom.comp_algebraMap
    have h3 : (e : (Localization.AtPrime x) →+* O) (algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ)) = algebraMap S O (algebraMap R S ϖ) := e.commutes _
    rw [h2, h3] at h1
    rw [h1]
    haveI : (Ideal.map (e : (Localization.AtPrime x) →+* O) (maximalIdeal (Localization.AtPrime x))).IsMaximal := Ideal.map_isMaximal_of_equiv e.toRingEquiv
    exact IsLocalRing.eq_maximalIdeal inferInstance
  · intro 𝔔' h𝔔'p h𝔔'le ht' hϖ'
    haveI := h𝔔'p
    have hdisj' : Disjoint (x.primeCompl : Set S) (𝔔' : Set S) := hdisj.mono_right h𝔔'le
    haveI : (𝔔'.map (algebraMap S (Localization.AtPrime x))).IsPrime := IsLocalization.isPrime_of_isPrime_disjoint x.primeCompl (Localization.AtPrime x) 𝔔' h𝔔'p hdisj'
    have hc' : (𝔔'.map (algebraMap S (Localization.AtPrime x))).comap (algebraMap S (Localization.AtPrime x)) = 𝔔' :=
      IsLocalization.under_map_of_isPrime_disjoint x.primeCompl (Localization.AtPrime x) h𝔔'p hdisj'
    have h1 : algebraMap S (Localization.AtPrime x) (algebraMap R S t) ∈ 𝔔'.map (algebraMap S (Localization.AtPrime x)) := Ideal.mem_map_of_mem _ ht'
    have h2 : algebraMap S (Localization.AtPrime x) (algebraMap R S ϖ) ∉ 𝔔'.map (algebraMap S (Localization.AtPrime x)) := by
      rw [← Ideal.mem_comap, hc']; exact hϖ'
    have h3 : 𝔔'.map (algebraMap S (Localization.AtPrime x)) ≠ maximalIdeal (Localization.AtPrime x) := by
      intro h; apply h2; rw [h, ← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ hϖx
    have h4 := huniq _ inferInstance h1 h2 h3
    rw [← hc', h4]

end CoreLocal

open IsLocalRing

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S] [Module.Free R S]
    (F : Type u) [Field F] [Algebra S F] [IsFractionRing S F] [Algebra K F] [Algebra R F]
    [IsScalarTower R K F] [IsScalarTower R S F] [Algebra.IsSeparable K F]
    (ϖ t : R) (hϖ0 : ϖ ≠ 0) (hmax : maximalIdeal R = Ideal.span {ϖ, t})
    [hϖp : (Ideal.span ({ϖ} : Set R)).IsPrime] (hϖ : IsDiscreteValuationRing (R ⧸ Ideal.span ({ϖ} : Set R)))
    (htp : (Ideal.span ({t} : Set R)).IsPrime) [CharZero (R ⧸ Ideal.span ({t} : Set R))]
    (hfib : IsDedekindDomain (S ⧸ Ideal.span ({algebraMap R S ϖ} : Set S)))
    (x : Ideal S) [x.IsMaximal]
    (hunr : ∀ (𝔔 : Ideal S) [𝔔.IsPrime], 𝔔 ≤ x → 𝔔.height = 1 → algebraMap R S t ∉ 𝔔 → Algebra.IsUnramifiedAt R 𝔔) :
    ∃ 𝔔 : Ideal S, 𝔔.IsPrime ∧ 𝔔 ≤ x ∧ algebraMap R S t ∈ 𝔔 ∧ algebraMap R S ϖ ∉ 𝔔 ∧
      (∀ (O : Type u) [CommRing O] [IsLocalRing O] [Algebra S O] [IsLocalization.AtPrime O x],
        Ideal.map (algebraMap S O) 𝔔 ⊔ Ideal.span {algebraMap S O (algebraMap R S ϖ)} = maximalIdeal O) ∧
      ∀ 𝔔' : Ideal S, 𝔔'.IsPrime → 𝔔' ≤ x → algebraMap R S t ∈ 𝔔' → algebraMap R S ϖ ∉ 𝔔' → 𝔔' = 𝔔 := by
  exact CoreLocal.main R K S F ϖ t hϖ0 hmax hϖ htp hfib x hunr

end S_Algebra_existsUnique_prime_le_map_sup_span_eq_maximalIdeal_of_isUnramifiedAt_of_isDedekindDomain_quotient_of_isLocalRing
end P2MW
export P2MW.S_Algebra_existsUnique_prime_le_map_sup_span_eq_maximalIdeal_of_isUnramifiedAt_of_isDedekindDomain_quotient_of_isLocalRing (solution)
