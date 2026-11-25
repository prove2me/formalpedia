-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FiniteVerticalGaussValuations
-- name    : Development_AbelianVarietyTheory_Proofs_HeightProofs_FiniteVerticalGaussValuations
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:11:54.296998+00:00
-- url     : https://prove2.me/theorems/d7f1755a-e94d-4d4e-9a23-96a6c8edd5e6
-- title:
--   Finite Vertical Gauss Valuations
-- statement:
--   Definitions and structural lemmas for Finite Vertical Gauss Valuations, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FiniteVerticalGaussValuations.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
namespace GlobalTheory
namespace VerticalGauss
open IsLocalRing IsDedekindDomain
noncomputable def extPrime {K : Type} [Field K] [NumberField K] (σ : Type)
    (la : HeightOneSpectrum (𝓞 K)) : Ideal (MvPolynomial σ (𝓞 K)) :=
  la.asIdeal.map MvPolynomial.C
instance extPrime_isPrime {K : Type} [Field K] [NumberField K] (σ : Type)
    (la : HeightOneSpectrum (𝓞 K)) : (extPrime σ la).IsPrime := by
  haveI := la.isPrime
  unfold extPrime
  rw [← Ideal.Quotient.isDomain_iff_prime]
  exact (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) la.asIdeal).symm.toMulEquiv.isDomain
end VerticalGauss
end GlobalTheory


