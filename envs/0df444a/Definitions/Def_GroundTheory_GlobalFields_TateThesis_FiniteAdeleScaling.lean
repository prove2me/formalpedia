-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
-- name    : GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:02:49.298802+00:00
-- url     : https://prove2.me/theorems/cbc52c86-ac30-4d24-a068-378156f328f2
-- title:
--   Finite Adele Scaling
-- statement:
--   Definitions and structural lemmas for Finite Adele Scaling, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
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
open NumberField IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
def finiteSingleUnits (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* (𝔸ᶠ[K])ˣ :=
  Units.map (IdeleGroup.finiteAdeleSingle v)
def finiteAdeleEval (x : HeightOneSpectrum (𝓞 K)) : 𝔸ᶠ[K] →* x.adicCompletion K :=
  RestrictedProduct.evalMonoidHom (fun w : HeightOneSpectrum (𝓞 K) ↦ w.adicCompletion K) x
def IsIntegralUnitAt (u : (𝔸ᶠ[K])ˣ) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  (u : 𝔸ᶠ[K]) v ∈ v.adicCompletionIntegers K ∧
    ((u⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) v ∈ v.adicCompletionIntegers K
def residueAt (v : HeightOneSpectrum (𝓞 K)) :
    (integralFiniteAdeles (𝓞 K) K).toAddSubgroup →+
      IsLocalRing.ResidueField (v.adicCompletionIntegers K) where
  toFun y := IsLocalRing.residue _ ⟨(y : 𝔸ᶠ[K]) v, y.2 v⟩
  map_zero' := by
    rw [← map_zero (IsLocalRing.residue (v.adicCompletionIntegers K))]
    rfl
  map_add' a b := by
    rw [← map_add]
    rfl
def integerUnitsToUnits (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletionIntegers K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom
end
end GroundTheory.Global


