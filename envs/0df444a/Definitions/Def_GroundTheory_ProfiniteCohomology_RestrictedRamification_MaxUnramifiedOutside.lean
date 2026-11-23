-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_MaxUnramifiedOutside
-- name    : GroundTheory_ProfiniteCohomology_RestrictedRamification_MaxUnramifiedOutside
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:04.181019+00:00
-- url     : https://prove2.me/theorems/fdc3c0fa-12b3-4f34-85f3-abd5b3e13f5f
-- title:
--   Max Unramified Outside
-- statement:
--   Definitions and structural lemmas for Max Unramified Outside, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/MaxUnramifiedOutside.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.ProfCoh
open NumberField IsDedekindDomain
variable {F : Type*} [Field F]
section Places
variable {L : Type*} [Field L] [Algebra F L]
def placesOver (S : Set (HeightOneSpectrum (𝓞 F))) : Set (HeightOneSpectrum (𝓞 L)) :=
  {w | ∃ v ∈ S, w.asIdeal.LiesOver v.asIdeal}
end Places
variable {Ω : Type*} [Field Ω] [Algebra F Ω]
def IsUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) (E : IntermediateField F Ω) : Prop :=
  ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal
variable (F Ω) in

noncomputable def maxUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) :
    IntermediateField F Ω :=
  ⨆ (E : IntermediateField F Ω) (_ : FiniteDimensional F E) (_ : IsUnramifiedOutside S E), E
variable (F Ω) in

abbrev galUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) :=
  Gal(maxUnramifiedOutside F Ω S / F)
end GroundTheory.ProfCoh


