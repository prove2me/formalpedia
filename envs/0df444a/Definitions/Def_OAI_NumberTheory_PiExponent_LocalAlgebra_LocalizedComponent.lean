-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_LocalizedComponent
-- name    : OAI_NumberTheory_PiExponent_LocalAlgebra_LocalizedComponent
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-08T11:15:20.782081+00:00
-- url     : https://prove2.me/theorems/bdec8e94-fc3a-4f5a-9aef-c76bd32695d0
-- title:
--   Prime radical membership in the minimal primes
-- statement:
--   This provider module contains the public Lean theorem stating that, for a commutative ring R and ideal I, if the radical of I is prime, then that radical belongs to the set of minimal prime ideals over I. The module includes the complete proved theorem body.
-- source:
--   OpenAI math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedComponent.lean, lines 9-12: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedComponent.lean#L9-L12

import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

namespace OAI

namespace PiExponentJets.W22

variable {R : Type*} [CommRing R]

theorem radical_mem_minimalPrimes (I : Ideal R) [I.radical.IsPrime] :
    I.radical ∈ I.minimalPrimes := by
  rw [← Ideal.radical_minimalPrimes, Ideal.minimalPrimes_eq_subsingleton_self]
  exact Set.mem_singleton _



end PiExponentJets.W22

end OAI


