-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PermLatticeDefs
-- name    : GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PermLatticeDefs
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:47:33.191491+00:00
-- url     : https://prove2.me/theorems/2e1768fb-7c12-5f3e-a24d-983abc094815
-- title:
--   Perm Lattice Defs
-- statement:
--   Definitions and structural lemmas for Perm Lattice Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/PermLatticeDefs.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
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
abbrev funPermAction (Γ X A : Type*) [Group Γ] [MulAction Γ X] [AddCommGroup A] :
    DistribMulAction Γ (X → A) where
  smul γ f x := f (γ⁻¹ • x)
  one_smul f := funext fun x => show f ((1 : Γ)⁻¹ • x) = f x by rw [inv_one, one_smul]
  mul_smul γ δ f := funext fun x =>
    show f ((γ * δ)⁻¹ • x) = f (δ⁻¹ • γ⁻¹ • x) by rw [mul_inv_rev, mul_smul]
  smul_zero γ := rfl
  smul_add γ f f' := rfl
end GroundTheory.ProfCoh


