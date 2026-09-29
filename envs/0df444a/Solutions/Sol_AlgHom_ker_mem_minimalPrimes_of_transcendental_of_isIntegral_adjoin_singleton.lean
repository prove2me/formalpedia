-- Prove2me | solution 1 for AlgHom.ker_mem_minimalPrimes_of_transcendental_of_isIntegral_adjoin_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/058c9e7d-ddbd-555b-81cb-b581c850fc0c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgHom_ker_mem_minimalPrimes_of_transcendental_of_isIntegral_adjoin_singleton

set_option autoImplicit false

theorem solution
    (A₀ R K : Type) [CommRing A₀] [CommRing R] [Field K] [Algebra A₀ R] [Algebra A₀ K]
    (j₀ : R) (ι : R →ₐ[A₀] K) (htr : Transcendental A₀ (ι j₀))
    (hint : Algebra.IsIntegral ↥(Algebra.adjoin A₀ {j₀}) R) :
    RingHom.ker ι.toRingHom ∈ (⊥ : Ideal R).minimalPrimes := by
  classical
  set R0 : Subalgebra A₀ R := Algebra.adjoin A₀ {j₀} with hR0
  have hR0f : ∀ r : ↥R0, ∃ f : Polynomial A₀, Polynomial.aeval j₀ f = (r : R) := by
    intro r
    have : (r : R) ∈ (Polynomial.aeval (R := A₀) j₀).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact r.2
    exact this

  have hcomap : (RingHom.ker ι.toRingHom).comap (algebraMap (↥R0) R) = ⊥ := by
    rw [eq_bot_iff]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker] at hr
    rw [Ideal.mem_bot]
    obtain ⟨f, hf⟩ := hR0f r
    have hf0 : Polynomial.aeval (ι j₀) f = 0 := by
      rw [Polynomial.aeval_algHom_apply, hf]; exact hr
    have hf00 : f = 0 := (transcendental_iff.mp htr) _ hf0
    apply Subtype.ext
    show (r : R) = 0
    rw [← hf, hf00, map_zero]

  haveI hprime : (RingHom.ker ι.toRingHom).IsPrime := RingHom.ker_isPrime _
  refine ⟨⟨hprime, bot_le⟩, ?_⟩
  rintro 𝔮 ⟨h𝔮, -⟩ hle
  by_contra hnot
  obtain ⟨x, hxp, hxq⟩ := Set.not_subset.mp hnot
  haveI := h𝔮
  have hlt := Ideal.comap_lt_comap_of_integral_mem_sdiff (R := ↥R0) hle ⟨hxp, hxq⟩ (hint.isIntegral x)
  rw [hcomap] at hlt
  exact not_lt_bot hlt

end S_AlgHom_ker_mem_minimalPrimes_of_transcendental_of_isIntegral_adjoin_singleton
end P2MW
export P2MW.S_AlgHom_ker_mem_minimalPrimes_of_transcendental_of_isIntegral_adjoin_singleton (solution)
