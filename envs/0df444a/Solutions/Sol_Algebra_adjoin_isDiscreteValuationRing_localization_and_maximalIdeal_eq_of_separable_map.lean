-- Prove2me | solution 1 for Algebra.adjoin.isDiscreteValuationRing_localization_and_maximalIdeal_eq_of_separable_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/729f9837-c69d-513f-be70-6d6699d7f507

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_adjoin_isDiscreteValuationRing_localization_and_maximalIdeal_eq_of_separable_map

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ConstExtCore

open Polynomial IsLocalRing

theorem isDiscreteValuationRing_localization_of_surjective_aeval
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {D : Type*} [CommRing D] [IsDomain D] [Algebra O D]
    (hinjD : Function.Injective (algebraMap O D))
    (e : D) (hgen : Function.Surjective (Polynomial.aeval (R := O) e))
    (f : O[X]) (hf : f.Monic) (hfe : aeval e f = 0) (hsep : (f.map (residue O)).Separable)
    (P : Ideal D) [P.IsPrime] (hP : (maximalIdeal O).map (algebraMap O D) ≤ P) :
    IsDiscreteValuationRing (Localization.AtPrime P) ∧
      maximalIdeal (Localization.AtPrime P) =
        ((maximalIdeal O).map (algebraMap O D)).map (algebraMap D (Localization.AtPrime P)) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h𝔪 : maximalIdeal O = Ideal.span {π} := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  set 𝔪D : Ideal D := (maximalIdeal O).map (algebraMap O D) with h𝔪D
  have h𝔪D_span : 𝔪D = Ideal.span {algebraMap O D π} := by
    rw [h𝔪D, h𝔪, Ideal.map_span, Set.image_singleton]

  haveI : IsNoetherianRing D := isNoetherianRing_of_surjective O[X] D (Polynomial.aeval e).toRingHom hgen

  set red : O[X] →+* (ResidueField O)[X] := Polynomial.mapRingHom (residue O) with hred
  have hred_surj : Function.Surjective red := Polynomial.map_surjective _ residue_surjective
  have hker𝔪 : ∀ p ∈ RingHom.ker red, aeval e p ∈ 𝔪D := by
    intro p hp
    rw [RingHom.mem_ker] at hp
    rw [Polynomial.aeval_eq_sum_range]
    refine Ideal.sum_mem _ fun i _ => ?_
    have hc : p.coeff i ∈ maximalIdeal O := by
      rw [← residue_eq_zero_iff]
      have := congrArg (fun r : (ResidueField O)[X] => r.coeff i) hp
      simpa only [hred, Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_zero] using this
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc)

  set Q : Ideal O[X] := P.comap (Polynomial.aeval e).toRingHom with hQ
  haveI hQp : Q.IsPrime := Ideal.comap_isPrime _ _
  have hmemQ : ∀ p : O[X], p ∈ Q ↔ aeval e p ∈ P := fun p => Iff.rfl
  have hker : RingHom.ker red ≤ Q := fun p hp => (hmemQ p).mpr (hP (hker𝔪 p hp))

  set Qb : Ideal (ResidueField O)[X] := Q.map red with hQb
  haveI hQbp : Qb.IsPrime := Ideal.map_isPrime_of_surjective hred_surj hker
  have hfQ : f ∈ Q := by rw [hmemQ, hfe]; exact P.zero_mem
  have hfb0 : red f ≠ 0 := (hf.map (residue O)).ne_zero
  have hfbQ : red f ∈ Qb := Ideal.mem_map_of_mem red hfQ
  have hQb0 : Qb ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hfbQ
    exact hfb0 hfbQ
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal Qb).principal
  have hg' : Qb = Ideal.span {g} := hg
  have hg0 : g ≠ 0 := by
    intro h
    apply hQb0
    rw [hg', h, Ideal.span_singleton_eq_bot]
  have hgprime : Prime g := (Ideal.span_singleton_prime hg0).mp (hg' ▸ hQbp)

  have hgf : g ∣ red f := by rw [← Ideal.mem_span_singleton, ← hg']; exact hfbQ
  obtain ⟨h, hfgh⟩ := hgf
  have hgh : ¬ g ∣ h := by
    intro hdvd
    have hsq : Squarefree (red f) := hsep.squarefree
    have hgg : g * g ∣ red f := by rw [hfgh]; exact mul_dvd_mul_left g hdvd
    exact hgprime.not_unit (hsq g hgg)
  have hhQ : h ∉ Qb := by
    intro hh
    rw [hg', Ideal.mem_span_singleton] at hh
    exact hgh hh
  obtain ⟨H, hH⟩ := hred_surj h
  have hHQ : H ∉ Q := by
    intro hHQ'
    exact hhQ (hH ▸ Ideal.mem_map_of_mem red hHQ')
  have hHP : aeval e H ∉ P := fun h' => hHQ ((hmemQ H).mpr h')

  have hclaim : ∀ x ∈ P, aeval e H * x ∈ 𝔪D := by
    intro x hx
    obtain ⟨p, rfl⟩ := hgen x
    have hpQ : p ∈ Q := (hmemQ p).mpr hx
    have hpb : red p ∈ Qb := Ideal.mem_map_of_mem red hpQ
    rw [hg', Ideal.mem_span_singleton] at hpb
    obtain ⟨c, hc⟩ := hpb
    obtain ⟨C, rfl⟩ := hred_surj c
    have hk : H * p - f * C ∈ RingHom.ker red := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_mul, hH, hc, hfgh]
      ring
    have hm := hker𝔪 _ hk
    rwa [map_sub, map_mul, map_mul, hfe, zero_mul, sub_zero] at hm

  have hmaxP : maximalIdeal (Localization.AtPrime P) = P.map (algebraMap D (Localization.AtPrime P)) :=
    (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hB : maximalIdeal (Localization.AtPrime P) = 𝔪D.map (algebraMap D (Localization.AtPrime P)) := by
    apply le_antisymm
    · rw [hmaxP, Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap]
      have hu : IsUnit (algebraMap D (Localization.AtPrime P) (aeval e H)) :=
        IsLocalization.map_units (Localization.AtPrime P) (⟨aeval e H, hHP⟩ : P.primeCompl)
      have hm : algebraMap D (Localization.AtPrime P) (aeval e H * x) ∈
          𝔪D.map (algebraMap D (Localization.AtPrime P)) := Ideal.mem_map_of_mem _ (hclaim x hx)
      rw [map_mul] at hm
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hm
    · rw [hmaxP]
      exact Ideal.map_mono hP

  haveI : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl (Localization.AtPrime P) inferInstance
  have hπD0 : algebraMap O D π ≠ 0 := fun h0 => hπ.ne_zero (hinjD (by rw [h0, map_zero]))
  have hinjDL : Function.Injective (algebraMap D (Localization.AtPrime P)) :=
    IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
  have hπL0 : algebraMap D (Localization.AtPrime P) (algebraMap O D π) ≠ 0 :=
    fun h0 => hπD0 (hinjDL (by rw [h0, map_zero]))
  have hmaxL : maximalIdeal (Localization.AtPrime P) =
      Ideal.span {algebraMap D (Localization.AtPrime P) (algebraMap O D π)} := by
    rw [hB, h𝔪D_span, Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField (Localization.AtPrime P) := by
    intro hF
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmaxL, Ideal.span_singleton_eq_bot] at hF
    exact hπL0 hF
  have hprinc : (maximalIdeal (Localization.AtPrime P)).IsPrincipal := by
    rw [hmaxL]
    exact ⟨⟨_, rfl⟩⟩
  exact ⟨((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 0 4).mpr hprinc, hB⟩

end ConstExtCore

theorem solution
    {O M : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing M] [IsDomain M] [Algebra O M]
    (hinj : Function.Injective (algebraMap O M))
    (e : M) (f : Polynomial O) (hf : f.Monic) (hfe : Polynomial.aeval e f = 0)
    (hsep : (f.map (IsLocalRing.residue O)).Separable)
    (P : Ideal ↥(Algebra.adjoin O ({e} : Set M))) [P.IsPrime]
    (hP : (IsLocalRing.maximalIdeal O).map (algebraMap O ↥(Algebra.adjoin O ({e} : Set M))) ≤ P) :
    IsDiscreteValuationRing (Localization.AtPrime P) ∧
      IsLocalRing.maximalIdeal (Localization.AtPrime P) =
        ((IsLocalRing.maximalIdeal O).map (algebraMap O ↥(Algebra.adjoin O ({e} : Set M)))).map
          (algebraMap ↥(Algebra.adjoin O ({e} : Set M)) (Localization.AtPrime P)) := by
  have hinjD : Function.Injective (algebraMap O ↥(Algebra.adjoin O ({e} : Set M))) := by
    intro a b h
    apply hinj
    have := congrArg (Subtype.val : ↥(Algebra.adjoin O ({e} : Set M)) → M) h
    simpa only [Subalgebra.coe_algebraMap] using this
  let e' : ↥(Algebra.adjoin O ({e} : Set M)) := ⟨e, Algebra.subset_adjoin (Set.mem_singleton e)⟩
  have hval : ∀ p : Polynomial O,
      ((Polynomial.aeval e' p : ↥(Algebra.adjoin O ({e} : Set M))) : M) = Polynomial.aeval e p := by
    intro p
    exact (Polynomial.aeval_algHom_apply (Algebra.adjoin O ({e} : Set M)).val e' p).symm
  have hgen : Function.Surjective (Polynomial.aeval (R := O) e') := by
    intro x
    have hx : (x : M) ∈ (Polynomial.aeval (R := O) e).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact x.2
    obtain ⟨p, hp⟩ := hx
    exact ⟨p, Subtype.ext (by rw [hval]; exact hp)⟩
  have hfe' : Polynomial.aeval e' f = 0 := Subtype.ext (by rw [hval, hfe]; rfl)
  exact ConstExtCore.isDiscreteValuationRing_localization_of_surjective_aeval hinjD e' hgen f hf hfe' hsep P hP

end S_Algebra_adjoin_isDiscreteValuationRing_localization_and_maximalIdeal_eq_of_separable_map
end P2MW
export P2MW.S_Algebra_adjoin_isDiscreteValuationRing_localization_and_maximalIdeal_eq_of_separable_map (solution)
