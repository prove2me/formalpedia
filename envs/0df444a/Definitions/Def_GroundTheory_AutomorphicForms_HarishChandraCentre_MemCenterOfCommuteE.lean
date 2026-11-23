-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
-- name    : GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:19.540018+00:00
-- url     : https://prove2.me/theorems/efc5bd1f-1001-4a72-b3aa-200a84e938cc
-- title:
--   Mem Center Of Commute E
-- statement:
--   Definitions and structural lemmas for Mem Center Of Commute E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemCenterOfCommuteE.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
abbrev gl (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev U (n : ℕ) := UniversalEnvelopingAlgebra ℂ (gl n)
variable {n : ℕ}
def E (a : Fin n × Fin n) : gl n := Matrix.single a.1 a.2 1
noncomputable def e (a : Fin n × Fin n) : U n := UniversalEnvelopingAlgebra.ι ℂ (E a)
noncomputable def word (w : List (Fin n × Fin n)) : U n := (w.map e).prod
end GroundTheory.Automorphic.HarishChandra


