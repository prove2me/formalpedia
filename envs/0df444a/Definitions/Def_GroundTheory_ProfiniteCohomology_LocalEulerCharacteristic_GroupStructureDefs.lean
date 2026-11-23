-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
-- name    : GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:22.192822+00:00
-- url     : https://prove2.me/theorems/a6f81062-68ef-4601-aee9-5012c4052d0e
-- title:
--   Group Structure Defs
-- statement:
--   Definitions and structural lemmas for Group Structure Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructureDefs.lean

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
def coprimePart (p : ℕ) (Q : Type*) [Group Q] : Subgroup Q :=
  Subgroup.closure {x : Q | (orderOf x).Coprime p}
def primaryPart (p : ℕ) (Q : Type*) [Group Q] : Subgroup Q :=
  Subgroup.closure {x : Q | ∃ n : ℕ, orderOf x = p ^ n}
variable {G : Type*} [Group G]
def coprimeQuotientPreimage (N : Subgroup G) [N.Normal] (p : ℕ) : Subgroup G :=
  (coprimePart p (G ⧸ N)).comap (QuotientGroup.mk' N)
def primaryQuotientPreimage (N : Subgroup G) [N.Normal] (p : ℕ) : Subgroup G :=
  (primaryPart p (G ⧸ N)).comap (QuotientGroup.mk' N)
def coprimeRelPreimage (N₀ N₁ : Subgroup G) [N₁.Normal] (p : ℕ) : Subgroup G :=
  (coprimeQuotientPreimage (N₁.subgroupOf N₀) p).map N₀.subtype
end GroundTheory.ProfCoh


