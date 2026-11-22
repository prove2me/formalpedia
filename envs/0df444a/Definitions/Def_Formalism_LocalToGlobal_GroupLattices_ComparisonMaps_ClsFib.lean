-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsFib
-- name    : Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsFib
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:33:15.027949+00:00
-- url     : https://prove2.me/theorems/3c0b9ea6-b17c-46b6-b7a4-b75cd7f4f5f6
-- title:
--   Cls Fib
-- statement:
--   Definitions and structural lemmas for Cls Fib, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsFib.lean

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.G.Cmp
open Formalism.UG
structure Fib {G Gp : Type} [Group G] [Group Gp] (K K' : Subgroup G) (Kp : Subgroup Gp) where
  j : Gp →* G
  pr : G →* Gp
  pr_j : ∀ g, pr (j g) = g
  j_mem : ∀ g, j g ∈ K'
  K_iff : ∀ x, x ∈ K ↔ x ∈ K' ∧ pr x ∈ Kp
namespace Fib
variable {G Gp : Type} [Group G] [Group Gp] {K K' : Subgroup G} {Kp : Subgroup Gp} (X : Fib K K' Kp) (H : Subgroup G)
def mkC (S : Subgroup G) (a : G) : ClassSet H S := DoubleCoset.mk H S a
variable (y : ClassSet H K' → G) (hy : ∀ i, mkC H K' (y i) = i) (hp : ∀ i, X.pr (y i) = 1)
end Fib
end Formalism.L2.G.Cmp


