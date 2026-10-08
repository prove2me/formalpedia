-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_QuotientLengthEquivalence
-- name    : OAI_NumberTheory_PiExponent_LocalAlgebra_QuotientLengthEquivalence
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-08T12:22:31.392492+00:00
-- url     : https://prove2.me/theorems/c81fa9b0-7469-4540-9950-03f3b0c00fe0
-- title:
--   Module length under a bijective semilinear map
-- statement:
--   Let R and S be rings, M an R-module and N an S-module. If sigma : R -> S is a surjective ring homomorphism and f : M -> N is a bijective sigma-semilinear map, then the module length of M over R equals the module length of N over S. No finiteness hypothesis on either length is required.
-- source:
--   OpenAI math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/QuotientLengthEquivalence.lean#L8-L15

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Length


namespace OAI

namespace PiExponentJets.W22

theorem length_eq_of_semilinear_bijective
    {R S M N : Type*} [Ring R] [Ring S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N]
    (σ : R →+* S) [RingHomSurjective σ]
    (f : M →ₛₗ[σ] N) (hf : Function.Bijective f) :
    Module.length R M = Module.length S N := by
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hf)]



end PiExponentJets.W22

end OAI


