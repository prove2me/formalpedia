-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FixedSubgroup
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FixedSubgroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:28.2055+00:00
-- url     : https://prove2.me/theorems/e76fd833-8997-43b1-9825-2d0dda8972ec
-- title:
--   Fixed Subgroup
-- statement:
--   Definitions and structural lemmas for Fixed Subgroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FixedSubgroup.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd :
    {A H M : Type} →
      [inst : CommRing A] →
        [inst_1 : Group H] →
          [inst_2 : AddCommGroup M] → [inst_3 : _root_.Module A M] → Representation A H M → Subgroup H → Submodule A M :=
  fun {_A _H _M} _ _ _ _ ρ K =>
    { carrier := {v | ∀ k ∈ K, ρ k v = v}
      add_mem' := fun {a b} ha hb k hk => by
        rw [map_add, ha k hk, hb k hk]
      zero_mem' := fun k _ => map_zero (ρ k)
      smul_mem' := fun c v hv k hk => by
        rw [map_smul, hv k hk] }


