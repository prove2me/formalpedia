-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationEmbeddingGeneratorEqOne
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationEmbeddingGeneratorEqOne
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T23:49:22.057467+00:00
-- url     : https://prove2.me/theorems/8867216c-47e3-445a-9f36-2702892c5ac6
-- title:
--   Valuation Embedding Generator Eq One
-- statement:
--   Definitions and structural lemmas for Valuation Embedding Generator Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValuationEmbeddingGeneratorEqOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
namespace GlobalTheory
theorem ringOfIntegers_map_mem_valuationSubring {K : Type} [Field K] [NumberField K]
    (A : ValuationSubring ℂ) (σ : K →+* ℂ) (x : 𝓞 K) : σ (x : K) ∈ A := by
  have h1 : IsIntegral ℤ (σ (x : K)) := (RingOfIntegers.isIntegral_coe x).map σ.toIntAlgHom
  have h2 : IsIntegral A (σ (x : K)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]
  exact y.2
noncomputable def ringOfIntegersToValuationSubring {K : Type} [Field K] [NumberField K]
    (A : ValuationSubring ℂ) (σ : K →+* ℂ) : 𝓞 K →+* A :=
  ((σ.comp (algebraMap (𝓞 K) K)).codRestrict A.toSubring
    (fun x => ringOfIntegers_map_mem_valuationSubring A σ x))
end GlobalTheory


