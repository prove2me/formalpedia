-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_ConductorIdeal
-- name    : GroundTheory_GlobalFields_TateThesis_ConductorIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:42.649259+00:00
-- url     : https://prove2.me/theorems/58a9ec54-88a9-4bb1-98b9-a1116f1bc01d
-- title:
--   Conductor Ideal
-- statement:
--   Definitions and structural lemmas for Conductor Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ConductorIdeal.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Conductor
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
open scoped NumberField.AdeleRing
namespace GroundTheory.Global
noncomputable section
section Ideals
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
end Ideals
namespace IdeleGroup
variable {K : Type*} [Field K] [NumberField K] {H : Type*} [Group H] [TopologicalSpace H]
def conductor (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) : Ideal (𝓞 K) :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), v.asIdeal ^ conductorExponentAt χ v
def idealLevel (𝔪 : Ideal (𝓞 K)) : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ :=
  finiteLevel fun v ↦ multiplicity v.asIdeal 𝔪
def ofFinite : (FiniteAdeleRing (𝓞 K) K)ˣ →* IdeleGroup K :=
  (ContinuousMulEquiv.symm (prodEquiv K)).toMulEquiv.toMonoidHom.comp (MonoidHom.inr _ _)
end IdeleGroup
end
end GroundTheory.Global


