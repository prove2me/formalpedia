-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
-- name    : Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:41.060807+00:00
-- url     : https://prove2.me/theorems/8c29f0dd-0767-4f4c-b79c-8ee4c3de9e58
-- title:
--   Reduction Lemma First
-- statement:
--   Definitions and structural lemmas for Reduction Lemma First, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionLemmaFirst.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SelectionLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Matrix
open scoped Matrix
noncomputable section
namespace Formalism.DivisionValues
namespace ReductionFirst
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def Tw (w : HeightOneSpectrum (𝓞 K)) : Submonoid (𝓞 K) where
  carrier := {s | s ∉ w.asIdeal ∧ cO K s ∉ w.asIdeal}
  one_mem' := by
    have h1 : (1 : 𝓞 K) ∉ w.asIdeal := fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    exact ⟨h1, by simpa using h1⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases w.isPrime.mem_or_mem h with h | h
      exacts [ha h, hb h]
    · rw [map_mul] at h
      rcases w.isPrime.mem_or_mem h with h | h
      exacts [ha' h, hb' h]
def InS (w : HeightOneSpectrum (𝓞 K)) (x : K) : Prop :=
  ∃ s ∈ Tw w, ∃ r : 𝓞 K, (s : K) * x = r
end ReductionFirst
end Formalism.DivisionValues


