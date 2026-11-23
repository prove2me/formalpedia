-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_Conductor
-- name    : GroundTheory_GlobalFields_TateThesis_Conductor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:57.107637+00:00
-- url     : https://prove2.me/theorems/d129d5ce-2aa2-4d57-a7e1-93e428d0b916
-- title:
--   Conductor
-- statement:
--   Definitions and structural lemmas for Conductor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Conductor.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LocalConductor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing RestrictedProduct
namespace GroundTheory.Global
noncomputable section
namespace IdeleGroup
variable {K : Type*} [Field K] [NumberField K]
def finiteComponent (v : HeightOneSpectrum (𝓞 K)) :
    (FiniteAdeleRing (𝓞 K) K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (_root_.RestrictedProduct.evalMonoidHom
    (fun w : HeightOneSpectrum (𝓞 K) ↦ w.adicCompletion K) v)
def finiteUnitsSingle (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  Units.map (finiteAdeleSingle v)
def finiteLevel (n : HeightOneSpectrum (𝓞 K) → ℕ) : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ :=
  ⨅ v, (unitsLevel v (n v)).comap (finiteComponent v)
section Character
variable {H : Type*} [Group H] [TopologicalSpace H]
def conductorExponentAt (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  conductorExponent v (χ.comp (finiteUnitsSingle v))
end Character
end IdeleGroup
end
end GroundTheory.Global


