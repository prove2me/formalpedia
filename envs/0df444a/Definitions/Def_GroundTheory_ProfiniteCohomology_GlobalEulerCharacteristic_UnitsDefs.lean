-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_UnitsDefs
-- name    : GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_UnitsDefs
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:58:47.140297+00:00
-- url     : https://prove2.me/theorems/21c3013c-f8d4-4d54-9725-74dd5e72efb4
-- title:
--   Units Defs
-- statement:
--   Definitions and structural lemmas for Units Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/UnitsDefs.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open NumberField IsDedekindDomain
abbrev repAction {G M : Type*} [Group G] [AddCommGroup M] (ρ : Representation ℤ G M) :
    DistribMulAction G M where
  smul g x := ρ g x
  one_smul x := by
    change ρ 1 x = x
    rw [map_one, Module.End.one_apply]
  mul_smul g h x := by
    change ρ (g * h) x = ρ g (ρ h x)
    rw [map_mul, Module.End.mul_apply]
  smul_zero g := map_zero (ρ g)
  smul_add g := map_add (ρ g)
variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
noncomputable abbrev sUnitAction (S : Set (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) :
    DistribMulAction (L ≃ₐ[K] L) (Additive (S.unit L)) :=
  repAction (GroundTheory.Global.sUnitRep S hS)
end GroundTheory.ProfCoh


