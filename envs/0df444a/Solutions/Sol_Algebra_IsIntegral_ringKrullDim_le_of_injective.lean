-- Prove2me | solution 1 for Algebra.IsIntegral.ringKrullDim_le_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/c78d04d4-3dbb-54fb-a1e5-d3c148847e9d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_IsIntegral_ringKrullDim_le_of_injective

set_option autoImplicit false

theorem solution
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R ≤ ringKrullDim S := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [ringKrullDim_eq_bot_of_subsingleton]; exact bot_le
  haveI : Nontrivial S := hinj.nontrivial

  have hbot : ∀ P : Ideal R, (⊥ : Ideal S).comap (algebraMap R S) ≤ P := by
    intro P x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    have : x = 0 := hinj (by rw [hx, map_zero])
    rw [this]; exact zero_mem _

  have key : ∀ n : ℕ, ∀ l : LTSeries (PrimeSpectrum R), l.length = n →
      ∃ l' : LTSeries (PrimeSpectrum S), l'.length = n ∧
        l'.last.asIdeal.comap (algebraMap R S) = l.last.asIdeal := by
    intro n
    induction n with
    | zero =>
      intro l hl
      obtain ⟨Q, -, hQ, hQc⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral l.last.asIdeal (⊥ : Ideal S) (hbot _)
      exact ⟨RelSeries.singleton _ ⟨Q, hQ⟩, rfl, by simpa using hQc⟩
    | succ n ih =>
      intro l hl
      have hne : l.length ≠ 0 := by omega
      obtain ⟨l'', hl'', hc⟩ := ih l.eraseLast (by simp [RelSeries.eraseLast_length, hl])
      have hrel : l.eraseLast.last < l.last := l.eraseLast_last_rel_last hne
      obtain ⟨Q, hQge, hQ, hQc⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral l.last.asIdeal l''.last.asIdeal
          (by rw [hc]; exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hrel.le)
      have hlt : l''.last < ⟨Q, hQ⟩ := by
        refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hQge) ?_
        intro heq
        have h1 : l''.last.asIdeal = Q := by rw [heq]
        have h2 : l.eraseLast.last.asIdeal = l.last.asIdeal := by rw [← hc, ← hQc, h1]
        exact (ne_of_lt hrel) (PrimeSpectrum.ext h2)
      refine ⟨l''.snoc ⟨Q, hQ⟩ hlt, by simp [RelSeries.snoc_length, hl''], ?_⟩
      simpa [RelSeries.last_snoc] using hQc
  rw [ringKrullDim, ringKrullDim, Order.krullDim_eq_iSup_length, Order.krullDim_eq_iSup_length]
  refine WithBot.coe_le_coe.mpr (iSup_le fun l => ?_)
  obtain ⟨l', hl', -⟩ := key l.length l rfl
  exact le_iSup_of_le l' (by rw [hl'])

end S_Algebra_IsIntegral_ringKrullDim_le_of_injective
end P2MW
export P2MW.S_Algebra_IsIntegral_ringKrullDim_le_of_injective (solution)
