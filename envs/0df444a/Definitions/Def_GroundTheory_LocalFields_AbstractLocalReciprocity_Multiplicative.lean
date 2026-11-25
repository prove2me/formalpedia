-- Prove2me | Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Multiplicative
-- name    : GroundTheory_LocalFields_AbstractLocalReciprocity_Multiplicative
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:47:05.861859+00:00
-- url     : https://prove2.me/theorems/b41299c2-5843-4fe9-9cac-c2f1482add10
-- title:
--   Multiplicative
-- statement:
--   Definitions and structural lemmas for Multiplicative, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Multiplicative.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.LocalField.Abstract
open ProfiniteInteger
namespace ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
namespace FrobeniusLift
omit [TotallyDisconnectedSpace G] in

def mul (s t : D.FrobeniusLift K) : D.FrobeniusLift K where
  elt := s.elt * t.elt
  mem := K.mul_mem s.mem t.mem
  deg := s.deg + t.deg
  deg_pos := Nat.add_pos_left s.deg_pos _
  deg_eq := by
    rw [map_mul, s.deg_eq, t.deg_eq, ← ofAdd_add]
    push_cast
    ring_nf
omit [TotallyDisconnectedSpace G] in

def ofDegOne {φ : G} (hφK : φ ∈ (K : Subgroup G))
    (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂)) : D.FrobeniusLift K where
  elt := φ
  mem := hφK
  deg := 1
  deg_pos := Nat.one_pos
  deg_eq := by rw [hdφ, one_mul]
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
end FrobeniusLift
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
section DegOne
end DegOne
section General
end General
end ClassFieldData
end GroundTheory.LocalField.Abstract


