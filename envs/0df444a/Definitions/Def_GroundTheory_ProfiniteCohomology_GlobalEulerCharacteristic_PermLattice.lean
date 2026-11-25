-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PermLattice
-- name    : GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PermLattice
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:55:23.91079+00:00
-- url     : https://prove2.me/theorems/1ef75edb-9772-5188-819a-cac60ea8523f
-- title:
--   Perm Lattice
-- statement:
--   Definitions and structural lemmas for Perm Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/PermLattice.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Lattice
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PermLatticeDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PermLatticeCharacter
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_CyclicSubtraction_apply_eq_of_cycSub_eq_zero__fe379387d69c

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
open Module Representation GroundTheory.Global
open scoped TensorProduct
universe u v
section Character
variable {k : Type*} {Γ : Type*} [Field k] [Group Γ]
end Character
section Lattice
variable {Γ : Type*} [Group Γ]
end Lattice
namespace AdditiveFunction
variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)
end AdditiveFunction
end GroundTheory.ProfCoh


