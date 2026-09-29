-- Prove2me | solution 1 for AlgHom.congruenceIdeal_ne_bot_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/98c34ede-a366-5c6b-80ef-c6fa55ff6311

import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Nilpotent.Lemmas
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgHom_congruenceIdeal_ne_bot_of_isReduced

set_option autoImplicit false

universe u v

open IsLocalRing

theorem solution
    {𝒪 : Type u} {T : Type v} [CommRing 𝒪] [IsDomain 𝒪]
    [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [IsNoetherianRing T] [IsReduced T]
    (πT : T →ₐ[𝒪] 𝒪) :
    (RingHom.ker πT).annihilator.map πT ≠ ⊥ := by
  classical
  set 𝔭 : Ideal T := RingHom.ker πT with h𝔭def
  haveI h𝔭prime : 𝔭.IsPrime := RingHom.ker_isPrime πT

  have hcomap : 𝔭.comap (algebraMap 𝒪 T) = ⊥ := by
    refine le_bot_iff.mp fun a ha => ?_
    rw [Ideal.mem_comap, h𝔭def, RingHom.mem_ker] at ha
    have ha' : πT (algebraMap 𝒪 T a) = 0 := ha
    rw [AlgHom.commutes] at ha'
    exact (Ideal.mem_bot).mpr ha'

  have hmin : 𝔭 ∈ minimalPrimes T := by
    refine ⟨⟨h𝔭prime, bot_le⟩, ?_⟩
    rintro Q ⟨hQ, -⟩ hQle
    by_contra hnot
    obtain ⟨x, hx𝔭, hxQ⟩ := SetLike.not_le_iff_exists.mp hnot
    haveI := hQ
    have hlt := Ideal.comap_lt_comap_of_integral_mem_sdiff (R := 𝒪) hQle ⟨hx𝔭, hxQ⟩
      (Algebra.IsIntegral.isIntegral x)
    rw [hcomap] at hlt
    exact not_lt_bot hlt

  have hfin : (minimalPrimes T).Finite := minimalPrimes.finite_of_isNoetherianRing T
  set s : Finset (Ideal T) := hfin.toFinset.erase 𝔭 with hsdef
  set I : Ideal T := s.inf id with hIdef
  have hI_ann : I ≤ 𝔭.annihilator := by
    intro t ht
    refine Submodule.mem_annihilator.mpr fun x hx => ?_
    have hmem : t * x ∈ sInf (minimalPrimes T) := by
      refine Submodule.mem_sInf.mpr fun Q hQ => ?_
      by_cases hQ𝔭 : Q = 𝔭
      · subst hQ𝔭; exact Ideal.mul_mem_left _ t hx
      · have hQs : Q ∈ s := Finset.mem_erase.mpr ⟨hQ𝔭, hfin.mem_toFinset.mpr hQ⟩
        have htQ : t ∈ Q := by
          have := (Finset.inf_le (f := id) hQs : I ≤ id Q) ht
          exact this
        exact Ideal.mul_mem_right x Q htQ
    have hnil : sInf (minimalPrimes T) = (⊥ : Ideal T) := by
      have h := Ideal.sInf_minimalPrimes (I := (⊥ : Ideal T))
      have h0 : (⊥ : Ideal T).radical = ⊥ := nilradical_eq_zero T
      rw [h0] at h
      exact h
    rw [hnil, Ideal.mem_bot] at hmem
    simpa [smul_eq_mul] using hmem

  have hI_not_le : ¬ I ≤ 𝔭 := by
    intro hle
    rcases s.eq_empty_or_nonempty with hs | hs
    · have hItop : I = ⊤ := by rw [hIdef, hs, Finset.inf_empty]
      exact h𝔭prime.ne_top (top_le_iff.mp (hItop ▸ hle))
    · obtain ⟨Q, hQs, hQle⟩ := (h𝔭prime.inf_le' (s := s) (f := id)).mp hle
      obtain ⟨hQ𝔭, hQmin⟩ := Finset.mem_erase.mp hQs
      have hQmin' : Q ∈ minimalPrimes T := hfin.mem_toFinset.mp hQmin
      have h𝔭leQ : 𝔭 ≤ Q := hmin.2 ⟨hQmin'.1.1, bot_le⟩ hQle
      exact hQ𝔭 (le_antisymm hQle h𝔭leQ)

  obtain ⟨t, htI, ht𝔭⟩ := SetLike.not_le_iff_exists.mp hI_not_le
  intro hbot
  have hmem : πT t ∈ (RingHom.ker πT).annihilator.map πT := Ideal.mem_map_of_mem _ (hI_ann htI)
  rw [hbot, Ideal.mem_bot] at hmem
  exact ht𝔭 (by rw [h𝔭def, RingHom.mem_ker]; exact hmem)

end S_AlgHom_congruenceIdeal_ne_bot_of_isReduced
end P2MW
export P2MW.S_AlgHom_congruenceIdeal_ne_bot_of_isReduced (solution)
