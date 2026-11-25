-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleIdealMeasure
-- name    : GroundTheory_GlobalFields_TateThesis_AdeleIdealMeasure
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:18:03.966207+00:00
-- url     : https://prove2.me/theorems/aae557f4-2ae7-4e9e-bccc-bbf1561d9d6e
-- title:
--   Adele Ideal Measure
-- statement:
--   Definitions and structural lemmas for Adele Ideal Measure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory Measure WithZero
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
def uniformizerAt (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletionIntegers K :=
  Classical.choose (IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K))
theorem irreducible_uniformizerAt (v : HeightOneSpectrum (𝓞 K)) :
    Irreducible (uniformizerAt v) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K))
theorem uniformizerAt_ne_zero (v : HeightOneSpectrum (𝓞 K)) :
    (uniformizerAt v : v.adicCompletion K) ≠ 0 := fun h ↦
  (irreducible_uniformizerAt v).ne_zero (Subtype.ext h)
def uniformizerUnit (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ :=
  Units.mk0 _ (uniformizerAt_ne_zero v)
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
def idealFiniteAdeles : AddSubgroup 𝔸ᶠ[K] where
  carrier := {x | ∀ v : HeightOneSpectrum (𝓞 K),
    Valued.v (x v) ≤ exp (-FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K))}
  zero_mem' v := by
    change Valued.v (0 : v.adicCompletion K) ≤ _
    rw [map_zero]
    exact zero_le
  add_mem' {a b} ha hb v :=
    (Valuation.map_add _ (a v) (b v)).trans (max_le (ha v) (hb v))
  neg_mem' {a} ha v := by
    change Valued.v (-(a v)) ≤ _
    rw [Valuation.map_neg]
    exact ha v
def idealSupport : Finset (HeightOneSpectrum (𝓞 K)) :=
  (Filter.eventually_cofinite.1
    (FractionalIdeal.finite_factors (I : FractionalIdeal (𝓞 K)⁰ K))).toFinset
def idealIdele : (𝔸ᶠ[K])ˣ :=
  ∏ v ∈ idealSupport I, finiteSingleUnits v
    (uniformizerUnit v ^ FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K))
end
end GroundTheory.Global


