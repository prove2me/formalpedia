-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PermLatticeCharacter
-- name    : GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PermLatticeCharacter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:47.285451+00:00
-- url     : https://prove2.me/theorems/81020649-bcfe-45d8-a807-2eda1f9195f9
-- title:
--   Perm Lattice Character
-- statement:
--   Definitions and structural lemmas for Perm Lattice Character, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/PermLatticeCharacter.lean

import Mathlib
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
open Module Representation
universe uk uG uU uV uW
variable {k : Type uk} {G : Type uG} [Field k] [Group G]
noncomputable def equivProdRight {U : Type uU} {V : Type uV} {W : Type uW} [AddCommGroup U]
    [Module k U] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (τ : Representation k G U) {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) : (τ.prod ρ).Equiv (τ.prod σ) :=
  Representation.Equiv.mk ((LinearEquiv.refl k U).prodCongr e.toLinearEquiv) fun g =>
    LinearMap.ext fun x => Prod.ext rfl (LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) x.2)
end GroundTheory.ProfCoh


